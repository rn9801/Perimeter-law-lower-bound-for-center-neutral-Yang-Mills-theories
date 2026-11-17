#!/usr/bin/env python3
"""Deny AF_UNIX socket creation for a Comparator process and its children.

This applies the address-family restriction recommended by Comparator's
current README, without requiring a systemd user bus in the cloud container.
Landrun still supplies the Comparator build/export filesystem sandbox.
"""

import ctypes
import errno
import os
import platform
import sys


class Instruction(ctypes.Structure):
    _fields_ = [("code", ctypes.c_ushort), ("jt", ctypes.c_ubyte),
                ("jf", ctypes.c_ubyte), ("k", ctypes.c_uint)]


class Program(ctypes.Structure):
    _fields_ = [("length", ctypes.c_ushort),
                ("instructions", ctypes.POINTER(Instruction))]


def main() -> None:
    if sys.platform != "linux" or platform.machine() != "x86_64":
        raise SystemExit("This seccomp launcher requires Linux x86_64")
    if len(sys.argv) < 2:
        raise SystemExit("Pass the command to run")
    # seccomp_data: syscall number at 0, architecture at 4, first argument at 16.
    # Reject other architectures and x32 syscall numbers; deny socket/socketpair
    # when the requested address family is AF_UNIX. Other calls pass to Landrun.
    rules = [
        (0x20, 0, 0, 4),
        (0x15, 1, 0, 0xC000003E),
        (0x06, 0, 0, 0x80000000),
        (0x20, 0, 0, 0),
        (0x35, 0, 1, 0x40000000),
        (0x06, 0, 0, 0x80000000),
        (0x15, 2, 0, 41),
        (0x15, 1, 0, 53),
        (0x06, 0, 0, 0x7FFF0000),
        (0x20, 0, 0, 16),
        (0x15, 0, 1, 1),
        (0x06, 0, 0, 0x00050000 | errno.EPERM),
        (0x06, 0, 0, 0x7FFF0000),
    ]
    instructions = (Instruction * len(rules))(*(Instruction(*r) for r in rules))
    program = Program(len(rules), instructions)
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(38, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "PR_SET_NO_NEW_PRIVS failed")
    if libc.prctl(22, 2, ctypes.byref(program), 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "PR_SET_SECCOMP failed")
    os.execvp(sys.argv[1], sys.argv[1:])


if __name__ == "__main__":
    main()
