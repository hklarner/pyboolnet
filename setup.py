

import os
import platform
import sys

from setuptools import setup, find_packages

from pyboolnet import VERSION

setup(
    name="pyboolnet",
    version=VERSION,
    description="Python toolbox for the generation, manipulation and analysis of Boolean networks.",
    author="Hannes Klarner",
    author_email="leevilux@yahoo.de",
    url="https://github.com/hklarner/pyboolnet",
    packages=find_packages(),
    include_package_data=True,
    package_data={
        "pyboolnet": [
            "binaries/*/*",
            "binaries/*/*/*",
            "repository/**/*"],
        "": ['version.txt'],
    },
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
