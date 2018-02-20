
from distutils.core import setup

import os

package_data_files = []

# adding dependency files
for root, dirnames, filenames in os.walk('PyBoolNet/Dependencies'):
    root = root.replace('PyBoolNet/Dependencies','Dependencies')
    package_data_files.extend([os.path.join(root,x) for x in filenames])

# adding repository files
for root, dirnames, filenames in os.walk('PyBoolNet/Repository'):
    root = root.replace('PyBoolNet/Repository','Repository')
    package_data_files.extend([os.path.join(root,x) for x in filenames])

# adding test files
for root, dirnames, filenames in os.walk('PyBoolNet/Tests/Files/Input'):
    root = root.replace('PyBoolNet/Tests','Tests')
    package_data_files.extend([os.path.join(root,x) for x in filenames])

setup(name          = "PyBoolNet",
      version       = "2.2.3",
      description   = "Python Toolbox for the Generation, Manipulation and Analysis of Boolean Networks.",
      author        = "Hannes Klarner",
      author_email  = "hannes.klarner@fu-berlin.de",
      url           = "https://github.com/hklarner/PyBoolNet",
      packages      = ["PyBoolNet",
                       "PyBoolNet.Tests",
                       "PyBoolNet.Utility",
                       "PyBoolNet.Repository",
                       ],
      package_data  = {'PyBoolNet': package_data_files},

      classifiers   = [
          "Programming Language :: Python",
          "License :: OSI Approved :: GNU Library or Lesser General Public License (LGPL)",
          "Development Status :: 3 - Alpha",
          "Intended Audience :: Science/Research",
          "Natural Language :: English",
          "Topic :: Scientific/Engineering :: Bio-Informatics",
          ],
      requires=['networkx (>=1.11)'],
      )
