

# Links
PyBoolNet manual on GITHUB:
- https://github.com/hklarner/PyBoolNet/blob/master/Docs/Sphinx/build/latex/PyBoolNet.pdf

Relative path to lcoal file:
- Sphinx/build/latex/PyBoolNet.pdf

# Sphinx Instructions

To compile the documentation with sphinx first create all figures with PyBoolNet:
```
$ cd Sphinx
$ python make_figures.py
```

Now call run sphinx:
```
$ make latexpdf
```
