**UWrMaxSat** is a quite new solver for MaxSAT and pseudo-Boolean problems. It has been created at the University of Wroclaw and can be characterized as a complete solver for partial weighted MaxSAT instances, and, independently, for linear pseudo-Boolean optimizing and decision ones.

When citing, always reference my [ICTAI 2020](https://www.ictai2020.org/) conference paper, bibtex record is [here](https://www.computer.org/csdl/api/v1/citation/bibtex/proceedings/1pP3sSVh3BS/922800a132).

================================================================================
### Quick Install

1. clone the repository into uwrmaxsat:  
    git clone https://github.com/marekpiotrow/UWrMaxSat uwrmaxsat

2. build the SAT solver:

    * 2.1 get COMiniSatPSChandrasekharDRUP.zip:  
        wget https://baldur.iti.kit.edu/sat-competition-2016/solvers/main/COMiniSatPSChandrasekharDRUP.zip  
    * 2.2 unzip and move:  
        unzip COMiniSatPSChandrasekharDRUP.zip  
        mv 'COMiniSatPS Chandrasekhar DRUP/cominisatps' .  
    * 2.3 apply uwrmaxsat/cominisatps.patch:  
        cd cominisatps  
        patch -p1 <../uwrmaxsat/cominisatps.patch  
    * 2.4 compile the SAT solver library:  
        cd simp  
        MROOT=.. make libr  
        cd ..  
        mkdir minisat ; cd minisat ; ln -s ../core ../simp ../mtl ../utils . ; cd ../..

3. build the MaxSat preprocessor:  
    * 3.1 clone the MaxPre repository:  
        git clone https://github.com/Laakeri/maxpre  
    * 3.2 compile it as a static library:  
        cd maxpre  
        sed -i 's/-g/-D NDEBUG/' src/Makefile  
        make lib  
        cd ..

4. build the UWrMaxSat solver (release version, statically linked):  
    cd uwrmaxsat  
    make config  
    make r

### Comments:

   - the executable file is: build/release/bin/uwrmaxsat

   - if you do not want to use MaxPre, skip the steps 3.1 and 3.2 and replace the last command in 4. with:
       MAXPRE=  make r

   - if you want to use unbounded weights in MaxSAT instances, remove # in config.mk in the first line 
     containing BIGWEIGHTS before running the last command

   - The program can be compiled with mingw64 g++ compiler in MSYS2 environment (https://www.msys2.org).

### Other SAT solvers

You can replace COMiniSatPS SAT solver with (A) CaDiCaL by Armin Biere or (B) Glucose 4.1 by Gilles Audemard 
and Laurent Simon - see steps 5(A) and 5(B) below.

* **5(A)** clone CaDiCaL and build UWrMaxSat with this SAT solver:  
    cd ..  
    git clone https://github.com/arminbiere/cadical  
    cd cadical  
    patch -p1 <../uwrmaxsat/cadical.patch  
    ./configure  
    make  
    cd ../uwrmaxsat  
    cp config.cadical config.mk  
    make clean  
    make r

* **5(B)** clone Glucose 4.1 and build UWrMaxSat with this SAT solver:  
    cd ..  
    wget https://www.labri.fr/perso/lsimon/downloads/softwares/glucose-syrup-4.1.tgz  
    tar zxvf glucose-syrup-4.1.tgz  
    cd glucose-syrup-4.1  
    patch -p1 <../uwrmaxsat/glucose4.1.patch  
    cd simp  
    MROOT=.. make libr  
    cd ..  
    mkdir minisat ; cd minisat ; ln -s ../core ../simp ../mtl ../utils . ; cd ../..  
    cd uwrmaxsat  
    cp config.glucose4 config.mk  
    make r

