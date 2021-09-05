

import os
import subprocess

GIT_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".git"))
ROOT = os.path.dirname(os.path.abspath(__file__))
PATH = os.path.join(ROOT, "version.txt")


def read_version_txt() -> str:
    with open(PATH, "r") as fp:
        return fp.readline()


def write_version_txt(version: str):
    with open(PATH, "w") as fp:
        fp.write(version)


def read_version_git() -> str:
    try:
        return subprocess.check_output(["git", f"--git-dir={GIT_DIR}", "describe", "--always"]).strip().decode("utf-8")
    except Exception as e:
        print(f"exception in reading git version: {e}")


def read_version() -> str:
    version = read_version_git()
    if not version:
        version = read_version_txt()

    return version


if __name__ == '__main__':
    print(read_version_txt())
