"""Bound in-flight work, preserve input order, and stop dispatch on failure."""
from concurrent.futures import CancelledError, FIRST_COMPLETED, ThreadPoolExecutor, wait
from threading import Event


def bounded_map(function, items, jobs=1, *, stop_event=None, return_exceptions=False, stop_on=()):
    if jobs < 1:
        raise ValueError('jobs must be positive')
    stop = stop_event if stop_event is not None else Event()
    values = list(items)
    results = [CancelledError('Work was not dispatched after an earlier failure') for _ in values]
    first_error = None
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        active = {}
        position = 0
        def submit():
            nonlocal position
            while position < len(values) and len(active) < jobs and not stop.is_set():
                active[pool.submit(function, values[position])] = position
                position += 1
        submit()
        try:
            while active:
                completed, _ = wait(active, return_when=FIRST_COMPLETED)
                for future in completed:
                    index = active.pop(future)
                    try:
                        results[index] = future.result()
                    except Exception as error:
                        results[index] = error
                        if not return_exceptions or isinstance(error, stop_on):
                            stop.set()
                            first_error = first_error or error
                submit()
        finally:
            stop.set()
    if first_error is not None and not return_exceptions:
        raise first_error
    return results
