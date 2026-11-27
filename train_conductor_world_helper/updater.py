"""Handles the auto updating of the tmx file."""
import logging
import os
import time
import typing

import watchdog.events
import watchdog.observers

logger = logging.getLogger(__name__)


class OverwrittenFileHandler(watchdog.events.FileSystemEventHandler):
    """Event handler that checks if a file is updated via overwriting."""

    def __init__(
        self,
        filename: os.PathLike,
        callable_on_overwrite: typing.Callable,
    ) -> None:
        self.filename = filename
        self.callable_on_overwrite = callable_on_overwrite

    def on_moved(
        self,
        event: watchdog.events.FileMovedEvent,
    ) -> None:
        logger.debug("File move detected.")
        if not event.is_directory and event.dest_path.endswith(self.filename):
            logger.debug("File moved was a directory and ends with `%s`", self.filename)
            self.callable_on_overwrite()


def poll_and_call_on_updates(
    filename: os.PathLike,
    callable_on_update: typing.Callable,
) -> None:
    """Runs the callable whenever the given file has been updated."""
    event_handler = OverwrittenFileHandler(
        filename=filename,
        callable_on_overwrite=callable_on_update,
    )
    observer = watchdog.observers.Observer()
    parent_directory = os.path.dirname(filename)
    logger.debug("Observing %s", parent_directory)
    observer.schedule(
        event_handler=event_handler,
        path=parent_directory,
    )
    logger.info("Starting polling to look for changes to %s...", filename)
    observer.start()
    try:
        while True:
            seconds = 1
            # Why sleep by 1 second?
            time.sleep(seconds)
            logger.debug("Waited %ss for changes to %s...", seconds, filename)
    except KeyboardInterrupt:
        observer.stop()
    observer.join()
