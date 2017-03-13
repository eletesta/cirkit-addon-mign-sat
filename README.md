# cirkit-addon-mign-sat
CirKit Addon for exact Synthesis 

Cirkit-addon-mign-sat is a CirKit Addon. This addon allows exact synthesis on mign, then `cirkit-addon-mign` needs to be installed before proceeding with this installation. 

After installing CirKit and cirkit-addon-mign-sat, clone this reposiroty inside CirKit `addons` directory. 

Then, from the build directory, perform the following actions: 

1. ccmake ..

2. enable the addon by toggling the flag at `enable_cirkit-addon-mign-sat`. 

3. Press `c` and then `g`.

4. make 

This procedure will add the exact_mign command. 
