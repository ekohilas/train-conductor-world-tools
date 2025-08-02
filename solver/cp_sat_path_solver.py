import json
from ortools.sat.python import cp_model
import time
import graphviz
import os

# WARNING: Runtime can be ~30 minutes

WIDTH = 49
HEIGHT = 55

# create grid graph of correct size
# dict[(x, y)] = list of neighbors
graph = {}
for x in range(WIDTH):
    for y in range(HEIGHT):
        graph[(x, y)] = []
        # add neighbors
        if x > 0:
            graph[(x, y)].append((x - 1, y))
        if x < WIDTH - 1:
            graph[(x, y)].append((x + 1, y))
        if y > 0:
            graph[(x, y)].append((x, y - 1))
        if y < HEIGHT - 1:
            graph[(x, y)].append((x, y + 1))
            
all_edges = {}
# create template datastructure for every edge in graph
for node in graph:
    for neighbor in graph[node]:
        # create edge
        edge = (node, neighbor)
        if edge not in all_edges:
            # create variable for this edge
            all_edges[edge] = None

all_nodes = list(graph.keys())

# get all ports and cities
this_dir = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(this_dir, '../data/tiles.json')) as f:
    tiles = json.load(f)
        
def manhattan_distance(node1, node2):
    """Calculate Manhattan distance between two nodes."""
    return abs(node1[0] - node2[0]) + abs(node1[1] - node2[1])
    
ports = {}
cities = {}
for tile in tiles:
    if tile['group'] == 'Location':
        if tile['type'] == 'City':
            cities[tile['name']] = (tile['x'], tile['y'])
        elif tile['type'] == 'Port':
            ports[tile['name']] = (tile['x'], tile['y'])
            
def calculate_distances(ports, cities):
    """Calculate distances from each port to each city."""
    distances = {}
    for port_name, (port_x, port_y) in ports.items():
        distances[port_name] = []
        for city_name, (city_x, city_y) in cities.items():
            distance = manhattan_distance((port_x, port_y), (city_x, city_y))
            distances[port_name].append({'name': city_name, 'distance': distance})
        # sort by distance
        distances[port_name].sort(key=lambda x: (x['distance']))
    return distances

distances = calculate_distances(ports, cities)
for port, city_list in distances.items():
    print(f"Distances from {port}:")    
    for x in distances[port][:11]:
        print(f"{x['name']},{x['distance']}")
    print()

def edge_in_square(edge, square_corner1, square_corner2, offset=0):
    """
    Check if edge is in square defined by two corners.
    EDIT: Added offset units to widen square in every direction, to account for the Rotterdam => Lyon problem
    """
    (x1, y1), (x2, y2) = edge
    square_x1, square_y1 = min(square_corner1[0], square_corner2[0])-offset, min(square_corner1[1], square_corner2[1])-offset
    square_x2, square_y2 = max(square_corner1[0], square_corner2[0])+offset, max(square_corner1[1], square_corner2[1])+offset
    return square_x1 <= x1 <= square_x2 and square_y1 <= y1 <= square_y2 and \
           square_x1 <= x2 <= square_x2 and square_y1 <= y2 <= square_y2

model = cp_model.CpModel()


# iterate over every port - city pair
all_edges_by_layer = {}
for port_name, (port_x, port_y) in ports.items():
    cities_by_distance = distances[port_name]
    active_outgoing_paths = []
    
    for i in range(10):
        city_name = cities_by_distance[i]['name']
        city_x, city_y = cities[city_name]

        # var to represent that a path is in use
        path_in_use = model.new_bool_var(f"indicator_{port_name}_{cities_by_distance[i]['name']}")
        active_outgoing_paths.append(path_in_use)

        
        #Rotterdam => Lyon is a straight line that goes through other cities. Therefore it's impossible to have that connection be the minimum distance.
        #It's also impossible to connect using only the interior square. So we'll give it a bit more room.
        if (city_name == 'Lyon' and port_name == 'Rotterdam'):
            in_square_offset = 3
        else:
            in_square_offset = 1
            
        # create a variable for each edge, representing whether path is taken
        all_edges_by_layer[(port_name, city_name)] = {edge: model.new_bool_var(f"{port_name}_{city_name}_{edge}") for edge in all_edges
                                                      if edge_in_square(edge, (port_x, port_y), (city_x, city_y), offset=in_square_offset)}
        
        # disallow going through cities or ports, other than the start and destination.
        for edge in all_edges_by_layer[(port_name, city_name)]:
            if edge[0] in (set(cities.values()) | set(ports.values())) - set([(port_x,port_y),(city_x,city_y)]):
                edge_var = all_edges_by_layer[(port_name, city_name)][edge]
                model.add(edge_var == 0)
            elif edge[1] in (set(cities.values()) | set(ports.values())) - set([(port_x,port_y),(city_x,city_y)]):
                edge_var = all_edges_by_layer[(port_name, city_name)][edge]
                model.add(edge_var == 0)
                
        source_vertex = all_nodes.index((port_x, port_y))
        target_vertex = all_nodes.index((city_x, city_y))
        
        # define circuit for this port-city pair
        circuit = [(all_nodes.index(u),all_nodes.index(v),var) for (u, v), var in all_edges_by_layer[(port_name, city_name)].items()]
        
        # add self-loops for all nodes except start and destination (indicates to the solver that these are not required to be part of the circuit)
        non_cities_ports = set(all_nodes) - set([(port_x,port_y),(city_x,city_y)])
        circuit += [(all_nodes.index(node), all_nodes.index(node), model.new_bool_var(f"self_loop_{node}")) for node in non_cities_ports] # add self-loops
        circuit += [(source_vertex, source_vertex, ~path_in_use), (target_vertex, target_vertex, ~path_in_use)]  # add self-loops for source and target
        
        # add forced connection between target and source
        circuit += [(target_vertex, source_vertex, path_in_use)]
        
        model.add_circuit(circuit)
    model.add(sum(active_outgoing_paths) == 9)

        
# create global layer that ors all edges (both directions) across all layers
all_edges_undirected = set([frozenset(edge) for edge in all_edges.keys()])
all_edges_global_undirected = {}
for edge in all_edges_undirected:
    node1, node2 = edge
    # create a variable for the edge in the global layer
    var = model.new_bool_var(f"global_edge_{edge}")
    all_edges_global_undirected[edge] = var
    
    # get all layer variables that correspond to this edge
    variables_for_edge = []
    for (port_name, city_name), edges in all_edges_by_layer.items():
        if (node1,node2) in edges:
            variables_for_edge.append(edges[(node1,node2)])
        if (node2,node1) in edges:
            variables_for_edge.append(edges[(node2,node1)])
    # var == True if any of the layer variables are True
    model.add_bool_or(variables_for_edge).only_enforce_if(var)
    model.add(sum(variables_for_edge) <= 0).only_enforce_if(~var)
    

# add constraints to global layer to ensure that each node has max 3 adjacent edge vars active
node_active_indicators = []
for node in all_nodes:
    # get all edges that are incident to this node
    incident_edges = [edge for edge in all_edges_global_undirected if node in edge]
    # create a list of variables for these edges
    incident_edge_vars = [all_edges_global_undirected[edge] for edge in incident_edges]
    # add constraint that at most 3 of these variables can be True
    model.add(sum(incident_edge_vars) <= 3)
    
    # check whether a new track tile is used here
    if node not in ports.values() and node not in cities.values():
        node_active_indicator = model.new_bool_var(f"node_active_{node}")
        model.add(sum(incident_edge_vars) > 0).only_enforce_if(node_active_indicator)
        model.add(sum(incident_edge_vars) == 0).only_enforce_if(~node_active_indicator)
        node_active_indicators.append(node_active_indicator)
    
# use graph distance for the individual distances
sum_individual_distances = sum(sum(all_edges_by_layer[key].values()) for key in all_edges_by_layer)

# first minimize individual distances, then minimize the total number of rail tiles.
#model.minimize(sum(all_edges_global_undirected.values())+ 1000*sum_individual_distances)
model.minimize(sum(node_active_indicators) + 1000 * sum_individual_distances)

solver = cp_model.CpSolver()
#print debugging information
solver.parameters.log_search_progress = True
solver.parameters.max_time_in_seconds = 60 * 60 * 2  # 2 hours

s = time.time()
status = solver.solve(model)
e = time.time()

print(f"Solved in {e - s:.2f} seconds")
    
def draw_graph_with_edges(graph, edges):
    dot = graphviz.Graph()
    for node in graph:
        if node in ports.values():
            name = [x for x in ports.keys() if ports[x] == node][0]
            dot.node(str(node), label=name, shape='box', style='filled',fillcolor='red', color='red')
        elif node in cities.values():
            name = [x for x in cities.keys() if cities[x] == node][0]
            dot.node(str(node), label=name, shape='ellipse',style='filled',fillcolor='lightblue', color='blue')
        else:
            dot.node(str(node))
    for edge in edges:
        dot.edge(str(edge[0]), str(edge[1]), color='black' if solver.value(all_edges_global_undirected[frozenset(edge)]) > 0.5 else 'white')
    
    # use faster engine
    dot.render('graph_with_edges', directory=this_dir, format='png', cleanup=True, engine='neato')
     
draw_graph_with_edges(graph, all_edges.keys())

# Print some stats about each connection
for port_name, (port_x, port_y) in ports.items():
    cities_by_distance = distances[port_name]
    
    for i in range(10):
        city_name = cities_by_distance[i]['name']
        city_x, city_y = cities[city_name]
        
        # print port-city pair if they are connected, and give the distance vs the manhattan distance
        if solver.value(sum(all_edges_by_layer[(port_name, city_name)].values())) > 0:
            print(f"{port_name+' -> '+city_name+':': <{30}} distance {solver.value(sum(all_edges_by_layer[(port_name, city_name)].values())): >{2}} vs manhattan {distances[port_name][i]['distance']: >{2}}")
        
        


