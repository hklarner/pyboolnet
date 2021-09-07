

import os


DIR_TEST_FILES_IN = os.path.join(os.path.abspath(os.path.dirname(__file__)), "files_input")
DIR_TEST_FILES_OUT = os.path.join(os.path.abspath(os.path.dirname(__file__)), "files_output")


def get_tests_path_in(fname: str) -> str:
    return os.path.abspath(os.path.join(DIR_TEST_FILES_IN, fname))


def get_tests_path_out(fname: str) -> str:
    return os.path.abspath(os.path.join(DIR_TEST_FILES_OUT, fname))
