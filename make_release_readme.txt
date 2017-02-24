
update all references to version in:
   - ./Docs/Sphinx/source/conf.py
   - ./Docs/Sphinx/source/Substitutions.rst
   - ./Docs/Sphinx/source/Installation.rst
   - ./setup.py
   - ./PyBoolNet/__init__.version()
   - ./make_release.sh $VERSION

you should be on branch "develop".
make final commits:
   $ git commit -a -m "last commit"
   $ git push

merge with master:
   $ git checkout master
   $ git merge --no-ff develop
   
add correct git tag:
   $ git tag -a v3.0
   
continue with branch develop:
   $ git checkout develop
