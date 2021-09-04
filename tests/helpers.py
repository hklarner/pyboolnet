

import os

ROOT_DIR_OUT = os.path.join(os.path.dirname(__file__), "files_output")
ROOT_DIR_IN = os.path.join(os.path.dirname(__file__), "files_input")


def get_tests_path_in(fname: str) -> str:
    return os.path.abspath(os.path.join(ROOT_DIR_IN, fname))


def get_tests_path_out(fname: str) -> str:
    return os.path.abspath(os.path.join(ROOT_DIR_OUT, fname))
