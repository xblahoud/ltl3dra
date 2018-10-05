V=2.4
wget -O buddy-$V.tar.gz https://sourceforge.net/projects/buddy/files/buddy/BuDDy%20$V/buddy-$V.tar.gz/download
tar -xzf buddy-$V.tar.gz
mv buddy-$V
cd buddy-$V
./configure
make
make install
ldconfig
cd ..
rm -rf buddy-$V buddy-$V.tar.gz
