from setuptools import setup
import os
from distutils.dir_util import copy_tree
import platform


package_data_files = []

# Handle PyBoolNet dependencies per platform
this_os = platform.system()
if "CONDA_BUILD" in os.environ:
    pyboolnet_dep_folder = os.path.join("dependencies", "conda")
elif this_os == "Linux":
    pyboolnet_dep_folder = os.path.join("dependencies", "linux64")
elif this_os == "Darwin":
    pyboolnet_dep_folder = os.path.join("dependencies", "mac64")
elif this_os == "Windows":
    pyboolnet_dep_folder = os.path.join("dependencies", "win64")
else:
    # no idea if we could get here?
    raise Exception

print(f"pyboolnet dependency folder = {pyboolnet_dep_folder}")

# copy dependencies to PyBoolNet/Dependencies
copy_tree(pyboolnet_dep_folder, os.path.join("pyboolnet", "dependencies"))

# adding dependency files
for root, dirnames, filenames in os.walk('pyboolnet/dependencies'):
    root = root.replace('pyboolnet/dependencies', 'dependencies')
    package_data_files.extend([os.path.join(root, x) for x in filenames])

# adding repository files
for root, dirnames, filenames in os.walk('pyboolnet/repository'):
    root = root.replace('pyboolnet/repository', 'repository')
    package_data_files.extend([os.path.join(root, x) for x in filenames])

# adding test files
for root, dirnames, filenames in os.walk('pyboolnet/tests/files/input'):
    root = root.replace('pyboolnet/Tests', 'Tests')
    package_data_files.extend([os.path.join(root, x) for x in filenames])

setup(name="pyboolnet",
      version="2.31.0",
      description="Python Toolbox for the Generation, Manipulation and Analysis of Boolean Networks.",
      author="Hannes Klarner",
      author_email="hannes.klarner@fu-berlin.de",
      url="https://github.com/hklarner/PyBoolNet",
      packages=["pyboolnet",
                "pyboolnet.tests",
                "pyboolnet.utility",
                "pyboolnet.repository",
                ],
      package_data={'PyBoolNet': package_data_files},

      classifiers=[
          "Programming Language :: Python",
          "License :: OSI Approved :: GNU Library or Lesser General Public License (LGPL)",
          "Development Status :: 3 - Alpha",
          "Intended Audience :: Science/Research",
          "Natural Language :: English",
          "Topic :: Scientific/Engineering :: Bio-Informatics",
      ],
      install_requires=[
          "networkx>=2.4",
          "matplotlib>=3.3.3",
          "pytest",
          "pyeda==0.28.0"
      ]
      )
