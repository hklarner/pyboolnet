
VERSION=2.1

echo "Creating releases for PyBoolNet ver $VERSION"
cp PyBoolNet/readme.md README.txt

echo
echo "Removing local Dependencies"
rm -rf PyBoolNet/Dependencies

echo
echo "Creating linux32 release"
cp -ap Dependencies/linux32/. PyBoolNet/Dependencies
python setup.py sdist
mv dist/PyBoolNet-$VERSION.tar.gz dist/PyBoolNet-$VERSION\_linux32.tar.gz
rm -rf PyBoolNet/Dependencies

echo
echo "Creating linux64 release"
cp -ap Dependencies/linux64/. PyBoolNet/Dependencies
python setup.py sdist
mv dist/PyBoolNet-$VERSION.tar.gz dist/PyBoolNet-$VERSION\_linux64.tar.gz
rm -rf PyBoolNet/Dependencies

echo
echo "Creating win64 release"
cp -ap Dependencies/win64/. PyBoolNet/Dependencies
python setup.py sdist
mv dist/PyBoolNet-$VERSION.tar.gz dist/PyBoolNet-$VERSION\_win64.tar.gz
rm -rf PyBoolNet/Dependencies

echo
echo "Creating mac64 release"
cp -ap Dependencies/mac64/. PyBoolNet/Dependencies
python setup.py sdist
mv dist/PyBoolNet-$VERSION.tar.gz dist/PyBoolNet-$VERSION\_mac64.tar.gz
rm -rf PyBoolNet/Dependencies

echo
echo "Restoring local Dependencies (linux32)"
cp -ap Dependencies/linux32/. PyBoolNet/Dependencies

echo
echo "Copying manual from PyBoolNet/Docs/Sphinx"
cp PyBoolNet/Docs/Sphinx/build/latex/PyBoolNet.pdf dist/PyBoolNet-$VERSION\_manual.pdf

echo
echo "make sure you changed version in PyBoolNet/Docs/Sphinx/source/conf.py to $VERSION"
echo "make sure you changed version in PyBoolNet/Docs/Sphinx/source/Substitutions.rst to $VERSION"
echo "make sure you changed version in PyBoolNet/Docs/Sphinx/source/Installation.rst to $VERSION"
echo "make sure you changed version in setup.py to $VERSION"















