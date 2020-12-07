import argparse
import logging
from argparse import Namespace
from pathlib import Path

from .plugins import add_command_subparsers, Command

# the following line imports modules so their commands can register themselves
from . import containerization, datalog, grammars, polytracker

logger = logging.getLogger("polytracker")

TEST_DIR = Path(__file__).parent.parent / "tests"

if (TEST_DIR / "test_polytracker.py").exists():
    import pytest

    class TestCommand(Command):
        name = "test"
        help = "run the PolyTracker tests"

        def run(self, args: Namespace):
            return pytest.main([str(TEST_DIR)])


def main():
    parser = argparse.ArgumentParser(
        description="PolyTracker can instrument programs to track dataflow and controlflow information through their "
        "execution, and process the resulting traces."
    )

    parser.add_argument("--version", "-v", action="store_true", help="print PolyTracker's version and exit")

    add_command_subparsers(parser)

    args = parser.parse_args()

    if not hasattr(args, "func"):
        if args.version:
            print(polytracker.version())
            return 0

        # TODO: Once we implement a REPL, instead of printing help, enter the REPL here
        parser.print_help()
        return 1

    retval = args.func(args)
    if retval is None:
        retval = 0
    elif not isinstance(retval, int):
        if retval:
            retval = 0
        else:
            retval = 1
    return retval


if __name__ == "__main__":
    exit(main())
