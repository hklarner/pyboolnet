


.. _installation_software:

Installation
============

Installation
============

Linux
-----

Download the latest release from

   * https://github.com/hklarner/PyBoolNet/releases
   
|software| is written in Python 2.7 and packaged using *Distutils*.
We recommend to install the package using *pip*::

   $ sudo pip install PyBoolNet-2.0_linux.tar.gz
   
which should place the package here::

   /home/<user>/.local/lib/python2.7.x/dist-packages/PyBoolNet
   
where ``<user>`` is the name you are logged in with (to find out, type ``whoami``).   
Use the option ``--user`` (this time literally, do not replace it with you actual user name) if you do not have sudo rights::

   $ pip install PyBoolNet-2.0.tar.gz --user
   
The package is likely going to be placed here::

   /usr/local/lib/python2.7.x/dist-packages/PyBoolNet

To install |software| using *Distutils* unpack *PyBoolNet-2.0.tar.gz* into a temporary folder and run::

   $ sudo python setup.py install

again, using the ``--user`` flag if you do not have sudo rights::

   $ python setup.py install --user
   
The locations should be the same as when installing with *pip*.

You should now be able to import |software|::

   $ python
   >>> import PyBoolNet
   >>>


.. note:: To remove |software| using *pip* run::

      $ pip uninstall PyBoolNet
   
   If you do not have *pip*, all files must be removed manually.   

.. note::

   |software| should also run with Python 3.
   
Windows
-------
Not available yet.

Mac
---
Not available yet.


Dependencies
------------

Most of what |software| does is written in pure Python but some crucial tasks, for example solving ASP problems or deciding CTL queries, are done using third party software.
If you are using Linux the dependencies should work out of the box.
Otherwise you will have to download the binaries that fit your OS and modify the paths to the executables.
The file that records the locations is called ``settings.cfg`` and located in the folder ``Dependencies`` of |software|.
The default location is::

   /usr/local/lib/python2.7/dist-packages/PyBoolNet/Dependencies/settings.cfg
   
The file is a standard configuration file of ``name = value`` pairs. The default is::

   [Executables]
   nusmv           = ./linux/NuSMV-a/NuSMVa
   gringo          = ./linux/gringo-4.4.0/gringo
   clasp           = ./linux/clasp-3.1.1/clasp-3.1.1-x86-linux
   bnet2prime      = ./linux/BNetToPrime/BNetToPrime
   dot             = /usr/bin/dot
   neato           = /usr/bin/neato
   fdp             = /usr/bin/fdp
   sfdp            = /usr/bin/sfdp
   circo           = /usr/bin/circo
   twopi           = /usr/bin/twopi
   convert         = /usr/bin/convert
   
Simply replace the default paths with the paths to your own installations.
Note that ``./`` indicates a relative path while ``/`` is an absolute path.
 
To test whether the dependencies are correctly installed, run::

   $ python
   >>> import PyBoolNet
   >>> PyBoolNet.Tests.dependencies.run()
   
For information on what to do when not all tests are OK see :ref:`Troubleshooting <installation_troubleshooting>`.
   
   
.. _installation_bnettoprime:

BNetToPrime
...........

BNetToPrime_ stands for "Boolean network to prime implicants".
It is necessary to compute the prime implicants of a Boolean network. The binaries and source are available at:

   * https://github.com/xstreck1/BNetToPrime

You can also compile BNetToPrime_ from source, see the tool's homepage on github for instructions.
Make sure to update the paths in ``settings.cfg``.

   
.. _installation_potassco:

Potassco
........

The Potassco answer set solving collection consists of the ASP solver clasp_ and the grounder gringo_, see :ref:`Gebser2011 <Gebser2011>`.
They are necessary to compute trap spaces by means of stable and consistent arc sets in the prime implicant graph, see :ref:`Klarner2015(a)<klarner2015trap>`.

.. note:: 
   The development of the Potassco solving collection is active with frequent releases.
   |software| is tested with two specific versions, clasp-3.1.1_ and gringo-4.4.0_, and we recommend you use them.

The binaries and source are available at:

   * https://sourceforge.net/projects/potassco/files/clasp/3.1.1
   * https://sourceforge.net/projects/potassco/files/gringo/4.4.0

You can also compile gringo_ and clasp_ from source or download 64bit binaries, see the tool's homepage on sourceforge for instructions.
Make sure to update the paths in ``settings.cfg``.


.. _installation_nusmv:

NuSMV
.....

NuSMV_ is a symbolic model checker that we use to decide LTL and CTL queries.
|software| requires the extension NuSMV-a_ for model checking with accepting states.

.. note:: 
   |software| is tested with NuSMV-a_.
   
Binaries and source available at:

   * https://github.com/hklarner/NuSMV-a
   
You can also compile NuSMV-a_ from source, see the tool's homepage on github for instructions.
Make sure to update the paths in ``settings.cfg``.
   

.. _installation_graphviz:   

Graphviz
........

The program *dot* is part of the graph visualization software Graphviz_ and available at

   * http://www.graphviz.org/
   
It is required to generate drawings of interaction graphs and state transition graphs.
To install it on Linux run::

   $ sudo apt-get install graphviz
   
   
.. _installation_imagemagick:

ImageMagick
...........

The program *convert* is part of the ImageMagick_ software suite which is part of most Linux distributions.
It is required to generate animations of trajectories in the state transition graph.
To install it on linux run::

   $ sudo apt-get install ImageMagick
   
ImageMagick_ is available at

   * http://www.imagemagick.org/
   

.. _installation_networkx:

NetworkX
........

NetworkX_ is a Python package and required for standard operations on directed graphs, e.g. computing strongly connected components,
deciding if a path between two nodes exists.
The package is available at:

   * https://networkx.github.io
   
To install it using *pip* run::

   $ sudo pip install networkx>=1.10

or::
   
   $ pip install networkx>=1.10 --user
   
if you do not have super user rights.
  
.. note::
   |software| is tested with NetworkX_ version 1.10 and older versions will almost surely not work.


.. _installation_boolnet:

BoolNet
.......
BoolNet_ is a library for R_ that is used for the construction, simulation and analysis of Boolean networks, see :ref:`Müssel2010 <Müssel2010>`.
It is not a required dependency of |software| but you need it if you want to convert *sbml-qual* files into *bnet* files.
To install it run::

   $ sudo R
   > install.packages("BoolNet")
   
select a CRAN mirror and wait for the download and installation to finish.
BoolNet_ is available at

   * https://cran.r-project.org/web/packages/BoolNet/index.html


.. _installation_ginsim:

GINsim
......

GINsim_ is a Java program for the construction and analysis of qualitative regulatory and signaling networks, see :ref:`Chaouiya2012 <Chaouiya2012>`.
Like BoolNet_, GINsim_ is not a required dependency of |software| but it has a useful model repository and to use GINsim_ models you need to export them as *sbml-qual* files which can then be converted using BoolNet_.
No installation required, just download the latest version (tested with version 2.9) and call::

   $ java -jar GINsim-2.9.3.jar
   
GINsim_ is available at

   * http://www.ginsim.org/
   

.. _installation_troubleshooting:   
   
Troubleshooting
---------------
permission denied
.................
If you get *permission denied* erros like::

   OSError: [Errno 13] Permission denied

you might have to change the mode of the files to make sure that they are executable.
Locate the directory that contains |Software| (see :ref:`Installation of PyBoolNet <installation_software>` above) and run::

   ../PyBoolNet$ chmod -R 744 Dependencies/
   ../PyBoolNet$ chmod -R +x Dependencies/
   ../PyBoolNet$
   
no such file or directory
.........................   
   
If you get *No such file or directory* errors you are likely on a 64 bit Linux distribution that does not have 32-bit support. Follow the instructions here:

   * http://askubuntu.com/questions/231479/no-such-file-when-running-a-32-bit-program-on-a-64-bit-system


   

.. include:: Substitutions.rst

  



