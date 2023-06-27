

import os
import platform
import sys
from distutils.dir_util import copy_tree

from setuptools import setup, find_packages

from pyboolnet import VERSION

PACKAGE_DATA_FILES = []
THIS_OS = platform.system()

if "CONDA_BUILD" in os.environ:
    pyboolnet_dep_folder = os.path.join("binaries", "conda")
elif THIS_OS == "Linux":
    pyboolnet_dep_folder = os.path.join("binaries", "linux64")
elif THIS_OS == "Darwin":
    pyboolnet_dep_folder = os.path.join("binaries", "mac64")
elif THIS_OS == "Windows":
    pyboolnet_dep_folder = os.path.join("binaries", "win64")
else:
    print(f"the operating system is not recognized: os={THIS_OS}")
    sys.exit()

print(f"pyboolnet dependency folder:  {pyboolnet_dep_folder}")

source = pyboolnet_dep_folder
destination = os.path.join("pyboolnet", "binaries")
copy_tree(src=source, dst=destination)
print(f"copy_tree: source={pyboolnet_dep_folder}, destination={destination}")

for root, _, filenames in os.walk("pyboolnet/binaries"):
    root = root.replace("pyboolnet/binaries", "binaries")
    PACKAGE_DATA_FILES.extend([os.path.join(root, x) for x in filenames])


for root, _, filenames in os.walk("pyboolnet/repository"):
    root = root.replace("pyboolnet/repository", "repository")
    PACKAGE_DATA_FILES.extend([os.path.join(root, x) for x in filenames])

print("package_data_files:")
for x in PACKAGE_DATA_FILES:
    print(x)

setup(
    name="pyboolnet",
    version=VERSION,
    description="Python Toolbox for the generation, manipulation and analysis of Boolean networks.",
    author="Hannes Klarner",
    author_email="hannes.klarner@fu-berlin.de",
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
