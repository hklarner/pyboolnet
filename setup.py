

import os
import platform
import sys
from distutils.dir_util import copy_tree

from setuptools import setup, find_packages

from pyboolnet import VERSION


PACKAGE_DATA_FILES = []
THIS_OS = platform.system()
SUBDIR_MAP = dict(
    Linux="linux64",
    Darwin="mac64",
    Windows="win64",
)

if "CONDA_BUILD" in os.environ:
    subdir = "conda"
else:
    try:
        subdir = SUBDIR_MAP[THIS_OS]
    except KeyError:
        print(f"the operating system is not recognized: os={THIS_OS}")
        sys.exit(1)

BINARIES_SOURCE_DIR = os.path.join("binaries", subdir)
print(f"detected os and binaries: {THIS_OS=}, {BINARIES_SOURCE_DIR=}")

BINARIES_TARGET_DIR = os.path.join("pyboolnet", "binaries")
copy_tree(src=BINARIES_SOURCE_DIR, dst=BINARIES_TARGET_DIR)
print(f"copy_tree: {BINARIES_SOURCE_DIR=}, {BINARIES_TARGET_DIR=}")

for root, _, filenames in os.walk(BINARIES_TARGET_DIR):
    root = root.replace("pyboolnet/binaries", "binaries")
    PACKAGE_DATA_FILES.extend([os.path.join(root, x) for x in filenames])

for root, _, filenames in os.walk("pyboolnet/repository"):
    root = root.replace("pyboolnet/repository", "repository")
    PACKAGE_DATA_FILES.extend([os.path.join(root, x) for x in filenames])

setup(
    name="pyboolnet",
    version=VERSION,
    description="Python toolbox for the generation, manipulation and analysis of Boolean networks.",
    author="Hannes Klarner",
    author_email="leevilux@yahoo.de",
    url="https://github.com/hklarner/pyboolnet",
    package_data={"pyboolnet": PACKAGE_DATA_FILES, "": ['version.txt']},
    packages=find_packages(),
    include_package_data=True,
    classifiers=[
        "Programming Language :: Python",
        "License :: OSI Approved :: GNU Library or Lesser General Public License (LGPL)",
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Science/Research",
        "Natural Language :: English",
        "Topic :: Scientific/Engineering :: Bio-Informatics"],
    install_requires=[
        "networkx>=2.4",
        "pytest",
        "click>=8.0.1",
        "matplotlib>=3.3.3",
    ],
    entry_points="""
        [console_scripts]
        pyboolnet=pyboolnet.cli.main:main
        """)
