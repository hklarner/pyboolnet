
For Developers
==============

The github repository contains all files you need to clone, devolop and make your own release of PyBoolNet.
Please contact me at |myemail| if you plan to do so.


How to Clone, Develop and Release
---------------------------------
**How to clone**:
You need to follow two branches, *master* and *develop*.
To clone from github run::

   $ git clone git@github.com:hklarner/PyBoolNet.git

   
To get the development branch run::

   $ cd PyBoolNet
   $ git checkout -b develop origin/develop


**How to develop**:
To develop you need to first copy the dependencies that fit your system from dependencies source folder ``./Dependencies`` into the package folder ``./PyBoolNet/Dependencies``.
For example::

   $ cp -a Dependencies/linux32/. PyBoolNet/Dependencies

To test your local version of PyBoolNet either make a release and install it,
or add the path to your local version before importing PyBoolNet.
Assume you cloned into ``/home/github/PyBoolNet``.
Use::

   import sys
   sys.path.insert(0,'/home/github/PyBoolNet/PyBoolNet')
   import PyBoolNet


To compile the manual you need Sphinx::

   $ apt-get install python-sphinx


To compile the manual::

   $ cd Docs/Sphinx
   $ make latexpdf

The link to the PDF file is in ``Docs/Sphinx``.


**How to make a release**:
Define your local OS in ``make_release.sh $LOCALOS``.
Update all references to the current version in
   - ``./Docs/Sphinx/source/conf.py``
   - ``./Docs/Sphinx/source/Substitutions.rst``
   - ``./Docs/Sphinx/source/Installation.rst``
   - ``./setup.py``
   - ``./PyBoolNet/__init__.version()``
   - ``./make_release.sh $VERSION``
   
You should be on branch *develop*.
Make final commits::

   $ git commit -a -m "last commit"
   $ git push


Merge with branch *master*::

   $ git checkout master
   $ git merge --no-ff develop

   
Add correct tag::

   $ git tag -a v3.0
   $ git push

 
Create Python packages::

   $ ./make_release

   
Packages will be created inside ``./dist`` 
   
Continue with branch develop::

   $ git checkout develop



  

.. include:: Substitutions.rst

