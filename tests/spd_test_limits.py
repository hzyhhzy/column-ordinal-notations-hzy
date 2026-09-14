"""Portable SPD-test wall-clock / 256-MiB peak-RSS guard, no background thread."""
import sys
from time import monotonic


def peak_mib():
    if sys.platform == 'win32':
        import ctypes
        from ctypes import wintypes
        class Counters(ctypes.Structure):
            _fields_ = [('cb',wintypes.DWORD),('faults',wintypes.DWORD)] + [
                (name,ctypes.c_size_t) for name in (
                    'peak','working','peak_paged','paged','peak_nonpaged',
                    'nonpaged','pagefile','peak_pagefile')]
        data = Counters()
        data.cb = ctypes.sizeof(data)
        call = ctypes.windll.psapi.GetProcessMemoryInfo
        call.argtypes = (wintypes.HANDLE,ctypes.POINTER(Counters),wintypes.DWORD)
        call.restype = wintypes.BOOL
        current = ctypes.windll.kernel32.GetCurrentProcess
        current.restype = wintypes.HANDLE
        if not call(current(),ctypes.byref(data),data.cb):
            raise OSError('Cannot enforce SPD test peak-memory guard')
        return data.peak/1048576
    import resource
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return peak/(1048576 if sys.platform == 'darwin' else 1024)


class Guard:
    def __init__(self,seconds=45,mib=256):
        self.started,self.seconds,self.mib = monotonic(),seconds,mib
        self.events = 0
        self.check()

    def check(self):
        if monotonic()-self.started>self.seconds:
            raise TimeoutError(f'SPD test {self.seconds}-second overall deadline')
        if peak_mib()>self.mib:
            raise MemoryError(f'SPD test {self.mib}-MiB peak-RSS bound')

    def tick(self):
        self.events += 1
        if self.events%2048 == 0:
            self.check()

    peak_mib = staticmethod(peak_mib)


def install(module,seconds=45,mib=256):
    guard = Guard(seconds,mib)
    original = module.Budget.tick
    def guarded_tick(budget):
        guard.tick()
        return original(budget)
    module.Budget.tick = guarded_tick
    return guard
