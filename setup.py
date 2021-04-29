from setuptools import setup
import os
from distutils.dir_util import copy_tree
import platform


package_data_files = []

if "CONDA_BUILD" not in os.environ:
    # PyBoolNet dependencies
    this_os = platform.system()
    if this_os == "Linux":
        pyboolnet_dep_folder = os.path.join("Dependencies", "linux64") 
    elif this_os == "Darwin":
        pyboolnet_dep_folder = os.path.join("Dependencies", "mac64") 
    elif this_os == "Windows":
        pyboolnet_dep_folder = os.path.join("Dependencies", "win64") 
    else:
        # no idea if we could get here?
        raise Exception

    print(f"PyBoolNet dependency folder = {pyboolnet_dep_folder}")

    # copy dependencies to PyBoolNet/Dependencies
    copy_tree(pyboolnet_dep_folder, os.path.join("PyBoolNet", "Dependencies"))

    # adding dependency files
    for root, dirnames, filenames in os.walk('PyBoolNet/Dependencies'):
        root = root.replace('PyBoolNet/Dependencies', 'Dependencies')
        package_data_files.extend([os.path.join(root, x) for x in filenames])

# adding repository files
for root, dirnames, filenames in os.walk('PyBoolNet/Repository'):
    root = root.replace('PyBoolNet/Repository', 'Repository')
    package_data_files.extend([os.path.join(root, x) for x in filenames])

# adding test files
for root, dirnames, filenames in os.walk('PyBoolNet/Tests/Files/Input'):
    root = root.replace('PyBoolNet/Tests', 'Tests')
    package_data_files.extend([os.path.join(root, x) for x in filenames])

setup(name="PyBoolNet",
      version="2.31.0",
      description="Python Toolbox for the Generation, Manipulation and Analysis of Boolean Networks.",
      author="Hannes Klarner",
      author_email="hannes.klarner@fu-berlin.de",
      url="https://github.com/hklarner/PyBoolNet",
      packages=["PyBoolNet",
                "PyBoolNet.Tests",
                "PyBoolNet.Utility",
                "PyBoolNet.Repository",
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
