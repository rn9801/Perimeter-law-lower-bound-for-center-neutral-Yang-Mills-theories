#!/usr/bin/env python3
"""Preserve child '--' arguments between Comparator v4.30 and current Landrun.

Only a command separator is added. Every sandbox permission passed by the
upstream Comparator is forwarded unchanged to the real Landrun binary.
"""

import os
import sys


def main() -> None:
    args = sys.argv[1:]
    unary = {"--best-effort", "-ldd", "-add-exec"}
    paired = {"--ro", "--rw", "--rwx", "--rox", "--env"}
    position = 0
    while position < len(args):
        flag = args[position]
        if flag in unary:
            position += 1
        elif flag in paired:
            if position + 1 >= len(args):
                raise SystemExit(f"Missing value for {flag}")
            position += 2
        elif flag.startswith("-"):
            raise SystemExit(f"Unexpected Comparator sandbox option: {flag}")
        else:
            break
    if position == len(args):
        raise SystemExit("Missing sandboxed command")
    binary = os.environ["GLUELUMP_LANDRUN_BINARY"]
    os.execv(binary, [binary, *args[:position], "--", *args[position:]])


if __name__ == "__main__":
    main()
