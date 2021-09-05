
import os
import subprocess
import sys
from typing import List

from pyboolnet.version import read_version_txt, write_version_txt, read_version_git

GIT_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".git"))
COMMIT = subprocess.check_output(["git", f"--git-dir={GIT_DIR}", "rev-parse", "HEAD"]).strip().decode("utf-8")
PORCELAIN = subprocess.check_output(["git", f"--git-dir={GIT_DIR}", "status", "--porcelain"]).decode("utf-8").split("\n")
MODIFIED = [x for x in PORCELAIN if " M " in x]
TAGS = subprocess.check_output(["git", f"--git-dir={GIT_DIR}", "tag"]).strip().decode("utf-8").split("\n")
INDENT = 8


def subprocess_run(command: List[str]) -> subprocess.CompletedProcess:
    return subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def print_process_output(command: List[str], process: subprocess.CompletedProcess, indent: int = INDENT):
    lines = [indent * " " + "command = " + " ".join(command)]
    lines += [indent * " " + line for line in [x for x in process.stdout.decode("utf-8").strip().split("\n") if x]]
    lines += [indent * " " + line for line in [x for x in process.stderr.decode("utf-8").strip().split("\n") if x]]
    print("\n".join(lines))


def repo_is_ready_for_release() -> bool:
    is_ok = len(MODIFIED) == 0
    print(f"repo is ready: {'OK' if is_ok else 'FAILED'}")
    if not is_ok:
        lines = [INDENT * " " + line for line in MODIFIED]
        print("\n".join(lines))

    return is_ok


def pytest_is_happy() -> bool:
    print("running pytest ..")
    command = ["python3", "-m", "pytest", "tests/"]

    result = subprocess_run(command=command)
    print(f"pytest is happy: {'OK' if result.returncode == 0 else 'FAIL'}")
    print_process_output(command=command, process=result)

    return result.returncode == 0


def autodoc_is_happy() -> bool:
    print("running autodoc ..")
    command = ["python3", "autodoc/autodoc.py"]

    result = subprocess_run(command=command)
    print(f"autodoc is happy: {'OK' if result.returncode == 0 else 'FAIL'}")
    print_process_output(command=command, process=result)

    return result.returncode == 0


def read_release_version():
    if len(sys.argv) > 1:
        release_version = sys.argv[1]
        print(f"release_version={release_version}")
        return release_version
    else:
        print("release_version=", end="")
        return input()


def read_release_message():
    print("release_message=", end="")
    return input()


def create_release_commit(version: str, message: str) -> bool:
    command = ["git", "commit", "-a", "-m", f"release {version}" + (f": {message}" if message else "")]

    result = subprocess_run(command=command)
    print(f"creating release commit: {'OK' if result.returncode == 0 else 'FAIL'}")
    print_process_output(command=command, process=result)

    return result.returncode == 0


def create_release_tag(tag: str) -> bool:
    command = ["git", "tag", tag, "-m", f"release {tag}"]

    result = subprocess_run(command=command)
    print(f"creating release tag: {'OK' if result.returncode == 0 else 'FAIL'}")
    print_process_output(command=command, process=result)

    return result.returncode == 0


def push_release() -> bool:
    command = ["git", "push"]

    result = subprocess_run(command=command)
    print(f"pushing release commit: {'OK' if result.returncode == 0 else 'FAIL'}")
    print_process_output(command=command, process=result)

    return result.returncode == 0


def push_tag() -> bool:
    command = ["git", "push", "--tags"]

    result = subprocess_run(command=command)
    print(f"pushing tag: {'OK' if result.returncode == 0 else 'FAIL'}")
    print_process_output(command=command, process=result)

    return result.returncode == 0


def reset_version_and_exit(reset_version: str):
    write_version_txt(version=reset_version)
    print(f"reset version: {reset_version}")
    sys.exit(1)


def bake_release_version_into_code(release_version: str) -> bool:
    write_version_txt(version=release_version)
    print("baking release version: OK")

    return True


def release_version_is_acceptable(current_version: str, release_version: str) -> bool:
    if release_version in TAGS:
        print("release tag is acceptable: FAIL (tag in use)")
        return False

    if release_version <= current_version:
        print(f"release tag is acceptable: FAIL (release version too small)")
        print("continue? (y/n)")
        return input() == "y"

    return True


def print_announcement(current_version: str, release_version: str):
    commit_messages = subprocess.check_output(["git", "log", '--pretty=format:"%s"', f"{current_version}..{release_version}"]).decode("utf-8").split("\n")
    print(f"## release {release_version}")
    for message in commit_messages[1:]:
        print(f" - {message[1:-1]}")

    print(f" - compare: [compare/{current_version}...{release_version}](https://github.com/LogicsSoftwareGmbH/VehicleRouting/compare/{current_version}...{release_version})")


if __name__ == '__main__':
    print(f"version according to git: {read_version_git()}")
    current_version = read_version_txt()
    print(f"version according to txt: {current_version}")
    release_version = read_release_version()
    release_message = read_release_message()

    if not release_version_is_acceptable(current_version=current_version, release_version=release_version):
        sys.exit(1)

    if not repo_is_ready_for_release():
        sys.exit(1)

    if not pytest_is_happy():
        sys.exit(1)

    if not autodoc_is_happy():
        sys.exit(1)

    if not bake_release_version_into_code(release_version=release_version):
        sys.exit(1)

    if not create_release_commit(version=release_version, message=release_message):
        reset_version_and_exit(reset_version=current_version)

    if not create_release_tag(tag=release_version):
        reset_version_and_exit(reset_version=current_version)

    if not push_release():
        reset_version_and_exit(reset_version=current_version)

    if not push_tag():
        reset_version_and_exit(reset_version=current_version)

    print_announcement(current_version=current_version, release_version=release_version)
