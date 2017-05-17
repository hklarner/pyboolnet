
VERSION=2.12
LOCALOS=linux32

echo "creating manual"
cd Docs/Sphinx
make latexpdf
cd ../..



echo "Creating releases for PyBoolNet ver $VERSION"
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
echo "Copying manual from PyBoolNet/Docs/Sphinx"
cp -v Docs/Sphinx/build/latex/PyBoolNet.pdf dist/PyBoolNet-$VERSION\_manual.pdf

echo
echo "Restoring local Dependencies ($LOCALOS)"
cp -vap Dependencies/$LOCALOS/. PyBoolNet/Dependencies

echo
echo "make sure you changed version in PyBoolNet/Docs/Sphinx/source/conf.py to $VERSION"
echo "make sure you changed version in PyBoolNet/Docs/Sphinx/source/Substitutions.rst to $VERSION"
echo "make sure you changed version in PyBoolNet/Docs/Sphinx/source/Installation.rst to $VERSION"
echo "make sure you changed version in PyBoolNet/__inti__.py to $VERSION"
echo "make sure you changed version in setup.py to $VERSION"














