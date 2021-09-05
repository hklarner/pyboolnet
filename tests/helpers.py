

import os


def get_tests_path_in(fname: str) -> str:
    return os.path.abspath(os.path.join(ROOT_DIR_IN, fname))


def get_tests_path_out(fname: str) -> str:
    return os.path.abspath(os.path.join(ROOT_DIR_OUT, fname))
