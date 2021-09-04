

import os
import platform
import sys
from distutils.dir_util import copy_tree

from setuptools import setup

from pyboolnet import VERSION

package_data_files = []
THIS_OS = platform.system()

if "CONDA_BUILD" in os.environ:
    pyboolnet_dep_folder = os.path.join("dependencies", "conda")
elif THIS_OS == "Linux":
    pyboolnet_dep_folder = os.path.join("dependencies", "linux64")
elif THIS_OS == "Darwin":
    pyboolnet_dep_folder = os.path.join("dependencies", "mac64")
elif THIS_OS == "Windows":
    pyboolnet_dep_folder = os.path.join("dependencies", "win64")
else:
    print(f"the operating system is not recognized: os={THIS_OS}")
    sys.exit()

print(f"pyboolnet dependency folder:  pyboolnet_dep_folder={pyboolnet_dep_folder}")

copy_tree(pyboolnet_dep_folder, os.path.join("pyboolnet", "dependencies"))


for root, dirnames, filenames in os.walk("pyboolnet/dependencies"):
    root = root.replace("pyboolnet/dependencies", "dependencies")
    package_data_files.extend([os.path.join(root, x) for x in filenames])


for root, dirnames, filenames in os.walk("pyboolnet/repository"):
    root = root.replace("pyboolnet/repository", "repository")
    package_data_files.extend([os.path.join(root, x) for x in filenames])


for root, dirnames, filenames in os.walk("pyboolnet/tests/files/input"):
    root = root.replace("pyboolnet/Tests", "Tests")
    package_data_files.extend([os.path.join(root, x) for x in filenames])

setup(
    name="pyboolnet",
    version=VERSION,
    description="Python Toolbox for the Generation, Manipulation and Analysis of Boolean Networks.",
    author="Hannes Klarner",
    author_email="hannes.klarner@fu-berlin.de",
    url="https://github.com/hklarner/PyBoolNet",
    packages=[
        "pyboolnet",
        "pyboolnet.tests",
        "pyboolnet.utility",
        "pyboolnet.repository"],
    package_data={
        "pyboolnet": package_data_files,
        "": ['version.txt']},
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
        "matplotlib>=3.3.3",
        "pytest",
        "pyeda==0.28.0",
        "click==7.1.2"],
    entry_points="""
        [console_scripts]
        pyboolnet=pyboolnet.command_line_tool.cli.main:main
        """)
