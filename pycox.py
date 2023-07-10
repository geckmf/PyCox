# ###########################################################################
#  PyCox-A Python version of chevie-gap. (Works for Python version >=3.6.)  #
#  Copyright (C) 2011-2014 Meinolf Geck                                     #
#                                                                           #
#  This program is free software: you can redistribute it and/or modify     #
#  it under the terms of the GNU General Public License as published by     #
#  the Free Software Foundation, either version 3 of the License, or        #
#  (at your option) any later version.                                      #
#                                                                           #
#  This program is distributed in the hope that it will be useful,          #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of           #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            #
#  GNU General Public License for more details.                             #
#                                                                           #
#  You should have received a copy of the GNU General Public License        #
#  along with this program.  If not, see <http://www.gnu.org/licenses/>.    #
# ###########################################################################
#  Import into python:       'from pycox import *'                          #
#  Cythonize:                                                               #
#     cp pycox.py cychv.pyx                                                 #
#     cython3 -a cychv.pyx                                                  #
#     gcc -shared -pthread -fPIC -fwrapv -O2 -Wall -fno-strict-aliasing \   #
#                            -I/usr/include/python3.4 -o cychv.so cychv.c   #
# ###########################################################################
import sys  # uses sys.write and sys.version
import time

from polynomials import lpol, ir, ir5, lcmcyclpol, rootof1
from matrices import (permmult, perminverse, decomposemat, flatlist,
                      matmult, scalmatmult, cartesian, transposemat,
                      displaymat, kroneckerproduct, redlusztigsymbolB,
                      ainvbipartition,
                      directsummat, flatblockmat, nextprime, idmat, matadd,
                      determinantmat, gcdex, inversematp,
                      partitiontuples, centraliserpartition,
                      dualpartition, differencepartitions, partitions)
from coxeter import (bruhat, coxeter, reflectionsubgroup, coxeterclasses,
                     bruhatperm, cartantypetomat, cartantotype, bruhatcoxelm,
                     affinecartanmat, reflections, longestperm, allelmchain,
                     allmats, conjugacyclasses, cartanmat, conjugacyclass,
                     involutions, allwords, redleftcosetreps,
                     allwordstrings, fusionconjugacyclasses, identifyclasses,
                     redrightcosetreps, conjgenperm, cyclicshiftorbit,
                     conjclassdata, conjtomin, testcyclicshift,
                     redinrightcoset)

BANNER = '''
┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
┃    A PYTHON VERSION OF CHEVIE-GAP FOR (FINITE) COXETER GROUPS     ┃
┃        (by Meinolf Geck,  version 1r6p180, 27 Jan 2014)           ┃
┃                                                                   ┃
┃    To get started type "help(coxeter)" or "help(allfunctions)";   ┃
┃    see also https://dx.doi.org/10.1112/S1461157012001064.         ┃
┃    For notes about this version type  "versioninfo(1.6)".         ┃
┃    Check www.mathematik.uni-stuttgart.de/~geckmf for updates.     ┃
┃                                                                   ┃
┃    Import into "sage" (9.8 or higher, www.sagemath.org) works.    ┃
┃                                                                   ┃
┃         The proposed name for this module is "PyCox".             ┃
┃                    All comments welcome!                          ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
'''
# print(BANNER)

# standard variable
v = lpol([1], 1, 'v')

# define our own print


def lprint(x):
    sys.stdout.write(x)
    sys.stdout.flush()


# enable syntax completion
try:
    import readline
except ImportError:
    print("Module readline not available.")
else:
    readline.parse_and_bind("tab: complete")

CURRENTVERSION = sys.version_info
if CURRENTVERSION.major == 3 and CURRENTVERSION.minor >= 6:
    from functools import reduce
    inp = input
else:
    raise RuntimeError("you need Python version 3.6 or higher")


def writeto(fname, l):
    import json
    with open(fname, 'w') as f:
        json.dump(l, f)
    print("finished")


def allfunctions():
    """
    ---------------------------------------------------------------------
            For more details type, for example, 'help(coxeter)'.
    ---------------------------------------------------------------------
    coxeter ..................... creates Coxeter group (as python class)
    cartanmat ............................... Cartan matrix (finite type)
    affinecartanmat ......................... Cartan matrix (affine type)
    cartantotype .................... type recognition of a Cartan matrix
    longestperm ............... longest element in a finite Coxeter group
    reflections ............... all reflections in a finite Coxeter group
    reflectionsubgroup ................ subgroup generated by reflections
    bruhat ....................................... Bruhat-Chevalley order
    conjugacyclasses .......................... of a finite Coxeter group
    fusionconjugacyclasses ............ fusion of classes from a subgroup
    conjtomin ................. conjugate to an element of minimal length
    coxeterclasses ............... coxeter classes of parabolic subgroups
    allmats ............... all elements (as matrices) up to given length
    allwords ......... all elements (as reduced words) up to given length
    allelmsproperty .................. all elements with a given property
    redrightcosetreps ......... distinguished right coset representatives
    redinrightcoset ........ reduce to distinguished coset representative
    redleftcosetreps ........... distinguished left coset representatives

    Characters:
    chartable ................. character table of a finite Coxeter group
    inducedchar ............ induced character from a reflection subgroup
    inductiontable .................. decomposition of induced characters
    ainvariants .................................. Lusztig's a-invariants
    classpolynomials ....... class polynomials for Iwahori-Hecke algebras
    poincarepol ..................................... Poincare polynomial
    heckechartable .......... character table of an Iwahori-Hecke algebra
    heckecharvalues ........ character values on arbitrary basis elements
    leadingcoefficients .................. Lusztig's leading coefficients
    heckecentraltable ................. table of central character values
    schurelms ................ Schur elements of an Iwahori-Hecke algebra
    lcmschurelms ............ least common multiple of the Schur elements
    fakedegree ............................... fake degree of a character
    involutionmodel ...... involution model of Kottwitz and Lusztig-Vogan
    dimBu ................... dimension of the variety of Borel subgroups

    Cells and Families:
    wgraph .................... Kazhdan-Lusztig W-graph (as python class)
    klpolynomials ........................... Kazhdan-Lusztig polynomials
    klcells ....................................... Kazhdan-Lusztig cells
    relklpols ...................... relative Kazhdan-Lusztig polynomials
    wgraphstarorbit ............... orbit of W-graph under star operation
    gentaucells ................... cells under generalised tau-invariant
    leftconnected ........ left-connected components of a set of elements
    leftcellleadingcoeffs .......... leading coefficients for a left cell
    distinguishedinvolutions .... distinguished involutions in left cells
    constructible..................... Lusztig's constructible characters
    lusztigfamilies .... Lusztig's families and the partial order on them
    specialpieces .............................. Lusztig's special pieces
    klcellreps .......................... basic information on left cells
    klcellrepelm ................... special representation of an element
    leftcellelm .......... the left cell (equal parameters) of an element

    Combinatorics:
    partitions ............................. all partitions of an integer
    dualpartition ......................... dual (or conjugate) partition
    centraliserpartition ........... centraliser order in symmetric group
    bipartitions .................. all pairs of partitions of an integer
    lusztigsymbolB ................. symbol associated with a bipartition
    redlusztigsymbolB ...... reduced symbol associated with a bipartition
    ainvbipartition ....................... the corresponding a-invariant
    partitiontuples .............. all tuples of partitions of an integer
    centralisertuple ....... order in wreath product with symmetric group

    Polynomials and numbers:
    intlcm ........................ least common multiple of two integers
    gcdex .................... extended greatest common divisor algorithm
    nextprime .................... next primer bigger than a given number
    zeta5 ............. quadratic extension generated by the golden ratio
    rootof1 ......................................... cyclotomic integers
    lpol ................... creates Laurent polynomial (as python class)
    lpolmod ............. creates truncated polynomials (as python class)
    interpolatepol ............................ interpolates a polynomial
    cyclpol ....................................... cyclotomic polynomial
    cycldec ........ decomposition into product of cyclotomic polynomials

    Utility functions:
    cartesian ............................ cartesian product of two lists
    flatlist ............................................. flatten a list
    displaymat .................... display matrix in a user-friendly way
    noduplicates ......................... removes duplicates from a list
    partitioncap ........... common refinement of two partitions of a set
    printfunction ................... print the source code of a function
    transposemat .................................. transpose of a matrix
    matmult, matadd .......................... multiply, add two matrices
    determinantmat ..................... determinant of an integer matrix
    kroneckerproduct .................. Kronecker product of two matrices
    directsummat ........................... block direct sum of matrices
    decomposemat ........................ block decomposition of a matrix
    blockLR .......................... block LR decomposition of a matrix
    test ................................................... a test suite
    writeto ............................................. write to a file

    (Note: This is not the complete list of all functions; the individual
     help menues may contain references to further functions available.)
    """
    print("#I Type 'help(allfunctions)'")
    return None


VG = """   This is intended to be the last major version of  PyCox 1.  (There
   will be further bug fix releases, but everything entirely new will
   go  into  what  may  eventually be called  PyCox 2.)  Now, the new
   things in this release are: the function 'displaymat' which allows
   for  a nice printing  of various  objects based on matrices, e.g.,
   character tables,  induction tables,  and so on.  There  is also a
   much improved version of the function  'distinguishedinvolutions':
   it can compute  (by a general method, and for the first time)  the
   set of distinguished involutions for type E8;  this takes about 18
   days and 22GB main memory.
                                                      MG, 23 Apr 2012

   Patch 1.61:
   The help to  'chartableD'  now contains a more precise description
   of the conventions used,  especially for the case where n is even.
   An error has been corrected in the list of characters  returned by
   the function 'libdistinv'.

   Patch 1.618:
   The behaviour of the  'range' function with respect to slicing has
   changed from Python 3.0 to 3.2.  This patch contains some fixes so
   that it works in all Python 3 versions. Also corrected a minor bug
   in decomposemat (the indices were not sorted before).

                                                      MG, 20 Dec 2012

   Patch 1.6180:
   Corrected an error in the function 'heckeirrdata' for type Dn with
   small value of n. Added function 'classmin' to compute elements of
   minimal length in a conjugacy class.  Improved  functions  to deal
   with generalised tau-invariants  ('gentaucells' and 'gentaureps').
   Added data on left cells for E8 and new functions for working with
   left and two-sided cells (equal parameter case); see 'klcellreps',
   'klcellrepelm' and 'leftcellelm'.

                                                      MG, 27 Jan 2014

   (For the previous version type 'versioninfo(1.5)'.)
   """

VF = """   This release contains, first of all, some bug fixes and minor (but
   hopefully useful) additions, like the function  'allelmsproperty'.
   There is now a simple arithmetic for cyctlotomic integers, so that
   we can deal with dihedral groups in general; see 'rootof1'. And it
   also contains some  basic support for Kazhdan-Lusztig polynomials,
   cells and  W-graphs; see 'klcells', 'wgraphs' and 'klpolynomials'.
   Here, we make systematic use of  the concept  of induced cells and
   relative  Kazhdan-Lusztig  polynomials.  The resulting algorithm is
   remarkably efficient.  For example,  the  function  'klcells'  can
   compute the  W-graphs  of all  left cells for groups of rank up to
   about 8 (except for type E8). Some timings:

            Type F4:     72 left cells, about   1 second.
            Type H4:    206 left cells, about 370 seconds.
            Type E6:    652 left cells, about  45 seconds.
            Type E7:   6364 left cells, about   4 hours.
            Type A8:   2620 left cells, about 140 seconds.
            Type D8:  11504 left cells, about   4 hours.
            Type B8:  15304 left cells, about  58 hours.

   (For B8 at least 9GB are required; otherwise, 4GB are sufficient.)
   The programs  are not  yet  completely optimised but,  still,  the
   ultimate challenge, i.e., the computation of the 101796 left cells
   in type E8, seems to remain out of reach for the time being.

                                                      MG, 27 Jan 2012

   The patch 1.51  contains a number of minor fixes;  it now also has
   an implementation of 'relklpols' for unequal parameters. (E.g., it
   computes all left cells in type F_4, for any choice of parameters,
   in about 5 seconds;  it  is  capable  of dealing with type B_n and
   unequal  parameters for  n  up to around 7.) A further addition is
   the function  'dimBu' which I had written years ago for gap-chevie
   and which is now included here.
                                                      MG, 04 Feb 2012

   (For the previous version type 'versioninfo(1.4)'.)
   """

VE = """   This module has now reached a state  where it contains a number of
   features which have never been included in the official gap-chevie
   release, for example:
      * Lusztig's constructible characters and families (this already
        appeared in version 1.1; see 'lusztigfamilies');
      * the algorithm for computing the sizes of special pieces  (see
        'specialpieces');
      * the computation of character values on central elements  (see
        'heckecentraltable').
   (However, there are also a number of features of gap-chevie  which
   are not yet available in this module; for example, Coxeter cosets,
   Kazhdan-Lusztig polynomials and  various things from Jean Michel's
   development version of gap-chevie.)  I intend to add  support  for
   Kazhdan-Lusztig cells and  their relative version  (with  possibly
   unequal parameters) to a later version.  I am certain that further
   extensive  checking and  experimenting is  required to  make these
   programs as robust as possible.  At least there is now, I believe,
   sufficient material to develop further applications.

                                                      MG, 30 Sep 2011

   (For the previous version type 'versioninfo(1.3)'.)
   """

VD = """   This version contains basic support for Iwahori-Hecke algebras and
   their characters;  see 'heckechartable' and the further references
   there. The functions are written in such a way that the parameters
   can  be any non-zero  elements in some  base ring. We also provide
   a simple  arithmetic for  Laurent polynomials in one variable (see
   'lpol'),  in order to be able  to work with  generic algebras  and
   their  characters.  If something more  efficient is required, then
   one has to import external modules (e.g., 'sympy')  or work within
   sage (an example is given in the help for 'classpolynomials').

   Another addition in this version is  a simple arithmetic  for  the
   quadratic extension generated by the golden  ratio  (1+sqrt(5))/2,
   so that we now have exact arithmetic for the types I2(5), H_3, and
   H_4; see 'zeta5'. This also provides a more user-friendly printing
   of the irrationalities.
                                                      MG, 23 Sep 2011

   (For the previous version type 'versioninfo(1.2)'.)
   """

VC = """   This version mainly contains bug fixes  and internal  improvements
   to some algorithms, in particular character tables of types A, B, D.
   For ranks at most 8 (i.e., cases that  are involved in exceptional
   types),  this now works reasonably very fast.  Some  examples  for
   larger ranks:

     chartable(coxeter("A", 15))  now takes about   5 seconds CPU.
     chartable(coxeter("D", 10))  now takes about  15 seconds CPU.
     chartable(coxeter("B", 11))  now takes about  65 seconds CPU.
     chartable(coxeter("A", 19))  now takes about  95 seconds CPU.
     lusztigfamilies(coxeter("E", 8)) takes about 100 seconds CPU.

   If this is not fast enough in some applications, then one needs to
   re-write  the  functions in  the gap  library file 'ctsymmet.g' in
   python.

   Also added some  utility functions:  'transposemat' (which made me
   learn quite a bit about python ...) and flatlist. Having seen  how
   transposemat performs,  I also revise my statement  in versioninfo
   1.0 concerning general list handling:  some operations take longer
   than in gap, but  others are faster,  for example, this version of
   transposemat.  The test suite still runs faster in python 2.7 than
   in 3.2.
                                                      MG, 02 Sep 2011

   (For the previous version type 'versioninfo(1.1)'.)
   """

VB = """   This second version now  includes  support  for ordinary character
   tables of finite Coxeter groups.  The material is developed to the
   point  where one can compute induce/restrict tables,  a-invariants
   and Lusztig's families in python. See the help for 'chartable' and
   'lusztigfamilies' for more details.

   The whole module works both in python 2.7 and 3.2, but it seems to
   run almost twice as fast in python 2.7 than in 3.2 !  (I have  not
   yet tried to find out why.)

   On the whole, the programmes work out so I intend to continue with
   this project. Due to other obligations, development will slow down
   now for a while. Some further testing and profiling is required to
   see where performance could be improved, e.g., in 'chartableB' and
   'fusionconjugacyclasses'. The next step  will be to  think about a
   package for polynomials, on which Hecke algebras,  their character
   tables and Kazhdan-Lusztig polynomials will rely.

                                                      MG, 28 Aug 2011

   (For the previous version type 'versioninfo(1.0)'.)
   """

VA = """   The original version of CHEVIE was developed for GAP3 (and MAPLE).
   This module  now is the result of  my efforts  (1) to learn one of
   the more  modern programming languages and  (2) to see if at least
   parts of the gap part of chevie can  be implemented in it. I chose
   python (version 2.7)  mainly  because of its popularity,  and then
   also because 'sage' is based on python; in particular, this module
   can just be imported into 'sage'.

   The functions in this version basically implement the purely group
   theoretical part: creation of a (possibly infinite) Coxeter group,
   working with the elements.  For finite  Coxeter  groups, there are
   functions for reflection subgroups and conjugacy classes.

   The main difficulty  was to  find good  replacements  for the fast
   permutation arithmetic in gap. It also seems that,  in a number of
   applications,  the general handling of lists is  considerably more
   efficient in gap than in python. Some  work will be needed to deal
   more properly with the  irrational numbers involved in type H3, H4
   and  dihedral types. (Currently  I just use  float numbers,  which
   appears to be ok for H3 and H4.) Overall, the functions work  with
   satisfactory efficiency, including type E8.

   Plans for the next version include:
    * basic  character table operations
    * Kazhdan-Lusztig polynomials
                                                      MG, 23 Aug 2011
   """


def versioninfo(nr):
    if nr > 1.6:
        print("not yet available")
    elif nr == 1.6:
        print(VG)
    elif nr == 1.5:
        print(VF)
    elif nr == 1.4:
        print(VE)
    elif nr == 1.3:
        print(VD)
    elif nr == 1.2:
        print(VC)
    elif nr == 1.1:
        print(VB)
    elif nr == 1.0:
        print(VA)
    else:
        print("no information available")


# ########################################################################
#  This file is organised in sections:
#  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#  Section 1: Numbers, polynomials, other utility functions
#  Section 2: Coxeter groups, Cartan matrices, reflections
#  Section 3: Characters, Schur elements, families
#  Section 4: Kazhdan-Lusztig cells
#  Section 5: Tests
#
# ########################################################################
#
# Section 1: Numbers, polynomials, other utility functions
#
# moved to zeta5, polynomials, matrices
# ########################################################################
#
# Section 2: Coxeter groups, Cartan matrices, reflections
# moved to coxeter
##########################################################################
#
# Section 3: Characters, Schur elements, families
#

# F inducedchar

def inducedchar(W, H, psi):
    """returns the values of the induced character Ind(psi) (from H to W)
    on the conjugacy classes of W, where the character psi is given by
    the list of its values on the conjugacy  classes of H.

    >>> W = coxeter("A", 5)
    >>> H = reflectionsubgroup(W, [0, 1, 2, 3])
    >>> c = conjugacyclasses(H)
    >>> c = conjugacyclasses(H)['reps']; c
    [[], [0], [0, 2], [0, 1], [0, 1, 3], [0, 1, 2], [0, 1, 2, 3]]
    >>> inducedchar(W, H, [(-1)**len(w) for w in c])  # induce sign character
    [6, -4, 2, 0, 3, -1, 0, -2, 0, 1, 0]
    """
    clW = conjugacyclasses(W)['classlengths']
    clH = conjugacyclasses(H)['classlengths']
    fus = fusionconjugacyclasses(H, W)
    ind = len(clW) * [0]
    for i in range(len(clW)):
        for j in range(len(clH)):
            if i == fus[j] and psi[j] != 0:
                ind[i] += (W.order * clH[j] * psi[j]) // (clW[i] * H.order)
    return ind

# chartablesymmetric


def chartablesymmetric(n):
    """returns the character table of the  symmetric group of degree n.
    The  rows and  columns  are indexed  by  the partitions  of n, as
    ordered in partitions(n). The function computes the  permutation
    characters on all  Young subgroups and then decomposes them into
    irreducibles.  (The  implementation is much less  efficient than
    that in gap3 but it reasonably works up to n around 15.)

    >>> partitions(4)
    [[1, 1, 1, 1], [2, 1, 1], [2, 2], [3, 1], [4]]
    >>> chartablesymmetric(4)
    [[1, -1, 1, 1, -1],
     [3, -1, -1, 0, 1],
     [2, 0, 2, -1, 0],
     [3, 1, -1, 0, -1],
     [1, 1, 1, 1, 1]]
    """
    W = coxeter("A", n - 1)
    pt = partitions(n)
    ti = []
    for mu in pt[::-1]:
        J = list(range(n))
        l = 0
        for i in mu:
            l += i
            J.remove(l - 1)
        H = reflectionsubgroup(W, J)
        ch = conjugacyclasses(H)
        cl = ch['classlengths']
        nam = [partitions(len(t[1]) + 1) for t in H.cartantype]
        fus = []  # more efficient than fusionconjugacyclasses
        for st in cartesian(nam):
            p = flatlist(st)
            p.sort(reverse=True)
            while sum(p) < n:
                p.append(1)
            fus.append(pt.index(p))
        H.fusions[W.cartanname]['classes'] = fus[:]
        neu = inducedchar(W, H, len(cl) * [1])
        for irr in ti:
            scal = sum(cl[c] * irr[fus[c]] for c in range(len(cl))) // H.order
            neu = [neu[i] - scal * irr[i] for i in range(len(neu))]
        ti.append(neu[:])
    return ti[::-1]


def oldsymm(n):
    W = coxeter("A", n - 1)
    pt = partitions(n)
    cw = conjugacyclasses(W)
    tr = []
    for mu in partitions(n):
        J = list(range(n))
        l = 0
        for i in mu:
            l += i
            J.remove(l - 1)
        H = reflectionsubgroup(W, J)
        ch = conjugacyclasses(H)
        nam = [partitions(len(t[1]) + 1) for t in H.cartantype]
        fus = []  # more efficient than fusionconjugacyclasses
        for st in cartesian(nam):
            p = flatlist(st)
            p.sort(reverse=True)
            while sum(p) < n:
                p.append(1)
            fus.append(pt.index(p))
        H.fusions[W.cartanname]['classes'] = fus[:]
        tr.append(inducedchar(W, H, len(ch['reps']) * [1]))
    ti = []
    for i in range(len(tr)):
        neu = tr[-i - 1][:]
        for j in range(i):
            scal = sum(cw['classlengths'][k] * ti[j][k] * neu[k]
                       for k in range(len(tr)) if neu[k] != 0) // W.order
            for k in range(len(tr)):
                neu[k] -= scal * ti[j][k]
        ti.append(neu)
    return ti[::-1]

# F cyclepermB


def wordtopermB(n, w):
    pw = range(2 * n)  # first signed permutation
    for i in w:
        if i == 0:
            pw[i], pw[n + i] = pw[n + i], pw[i]
        else:
            pw[i - 1], pw[i] = pw[i], pw[i - 1]
            pw[n + i - 1], pw[n + i] = pw[n + i], pw[n + i - 1]
    return pw[:n]     # now roots


def chartablehalfC(n, other=False):
    """returns the part of the character table  of a  Coxeter group of
    type B whose rows are labelled by all bipartitions (alpha, beta)
    where alpha is empty (or beta is empty if the optional argument
    'other' is set to True.
    """
    ti = transposemat(chartablesymmetric(n))
    p = partitions(n)
    if other:
        cw = conjugacyclasses(coxeter("C", n))['reps']
    nti = []
    for mu, pt_mu in enumerate(partitiontuples(n, 2)):
        a = flatlist(pt_mu)
        a.sort(reverse=True)
        if not other:
            nti.append(ti[p.index(a)])
        else:
            if not cw[mu].count(0) % 2:
                nti.append(ti[p.index(a)])
            else:
                nti.append([-x for x in ti[p.index(a)]])
    return transposemat(nti)


def chartableB(n, verbose=False):
    """returns the character table of the finite Coxeter group of type
    B_n.  The rows and  columns are indexed  by  pairs of partitions
    of n, as ordered in partitiontuples(n, 2). The function proceeds
    by inflating characters of direct products  of groups of type A
    to direct products of groups of type B and then inducing to the
    whole group (see [Ge-Pf, 5.5.4]).

    (The implementation is less efficient than that in  gap3 but it
    reasonably works for  values  of n  up to around 10.)

    >>> list(partitiontuples(3, 2))
    [[[1, 1, 1], []], [[1, 1], [1]], [[1], [1, 1]], [[], [1, 1, 1]],
     [[2, 1], []], [[1], [2]], [[2], [1]], [[], [2, 1]], [[3], []], [[], [3]]]
    >>> chartableB(3)
    [[1, 1, 1, 1, -1, -1, -1, -1, 1, 1],
     [3, 1, -1, -3, -1, -1, 1, 1, 0, 0],
     [3, -1, -1, 3, -1, 1, -1, 1, 0, 0],
     [1, -1, 1, -1, -1, 1, 1, -1, 1, -1],
     [2, 2, 2, 2, 0, 0, 0, 0, -1, -1],
     [3, -1, -1, 3, 1, -1, 1, -1, 0, 0],
     [3, 1, -1, -3, 1, 1, -1, -1, 0, 0],
     [2, -2, 2, -2, 0, 0, 0, 0, -1, 1],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [1, -1, 1, -1, 1, -1, -1, 1, 1, -1]]

    See also 'heckevalueB'.
    """
    W = coxeter("C", n)     # use C_n because of B_2=C_2 convention.
    pt = list(partitiontuples(n, 2))
    refls = reflections(W)
    wrho = [[0]]
    for i in range(n - 1):
        wrho.append([i + 1] + wrho[i] + [i + 1])
    rho = [refls.index(W.wordtoperm(p)) for p in wrho]
    ti = chartablehalfC(n)
    labels = [[p, []] for p in partitions(n)]
    if n >= 10:
        if verbose:
            lprint('#I +')
    for a in range(1, n):  # type C_a x C_{n-a}
        H = reflectionsubgroup(W, list(range(a)) + [rho[a]] + list(range(a + 1, n)))
        l0 = len(H.cartantype[0][1])
        l1 = len(H.cartantype[1][1])
        fus = []  # much faster than fusionconjugacyclasses
        for t in cartesian(list(partitiontuples(l0, 2)),
                           list(partitiontuples(l1, 2))):
            x = flatlist(t[0][0] + t[1][0])
            x.sort(reverse=True)
            y = flatlist(t[0][1] + t[1][1])
            y.sort(reverse=True)
            fus.append(pt.index([x, y]))
        H.fusions[W.cartanname]['classes'] = fus[:]
        if 0 in H.cartantype[0][1]:
            f0, f1 = False, True
            labels.extend([[p[0], p[1]] for p in cartesian(partitions(l0),
                                                          partitions(l1))])
        else:
            f0, f1 = True, False
            labels.extend([[p[1], p[0]] for p in cartesian(partitions(l0),
                                                          partitions(l1))])
        ti.extend([inducedchar(W, H, psi) for psi in
             kroneckerproduct(chartablehalfC(l0, other=f0),
                              chartablehalfC(l1, other=f1))])
        if verbose and n >= 10:
            lprint('+')
    ti.extend(chartablehalfC(n, other=True))
    labels.extend([[[], p] for p in partitions(n)])
    if verbose and n >= 10:
        lprint('\n')
    return [ti[labels.index(mu)] for mu in pt]

# older version


def chartableBold(n):
    """returns the character table of the finite Coxeter group of type
    B_n.  The rows and  columns are indexed  by  pairs of partitions
    of n, as ordered in partitiontuples(n, 2). The function computes
    the  permutation characters on  suitable  reflection  subgroups
    (products  of various  types B and D,  see [Ge-Pf, 5.5.3])  and
    then decomposes them into irreducibles.  (The implementation is
    much less  efficient than that in  gap3 but it reasonably works
    for  values of n  up to around 8; it is also an excellent  test
    for 'reflectionsubgroup' and 'fusionconjugacyclasses').
    """
    W = coxeter("C", n)
    cw = conjugacyclasses(W)
    cycw = [W.cycletyperoots(W.wordtoperm(w)) for w in cw['reps']]
    refls = reflections(W)
    rho = [[0]]
    trho = [[0, 1, 0]]
    for i in range(n - 2):
        rho.append([i + 1] + rho[i] + [i + 1])
        trho.append(rho[i + 1] + [i + 2] + rho[i + 1])
    rho.append([n - 1] + rho[n - 2] + [n - 1])
    rho = [refls.index(W.wordtoperm(p)) for p in rho]
    trho = [refls.index(W.wordtoperm(p)) for p in trho]
    pt = list(partitiontuples(n, 2))
    binv = [2 * sum(i * mu[0][i] for i in range(len(mu[0]))) + 2 * sum(i * mu[1][i]
                     for i in range(len(mu[1]))) + sum(mu[1]) for mu in pt]
    nn = list(range(len(binv)))
    nn.sort(key=(lambda i: binv[i]), reverse=True)
    ti = []
    for k in nn:
        mu = pt[k]
        J = list(range(1, n + 1))
        l = 0
        for i in dualpartition(mu[0]):
            if i >= 2:
                J.append(trho[l])
            l += i
            J.remove(l)
        for i in dualpartition(mu[1]):
            J.append(rho[l])
            l += i
            J.remove(l)
        H = reflectionsubgroup(W, J)
        fus = []
        ch = conjugacyclasses(H)
        cl = ch['classlengths']
        f = H.fusions[W.cartanname]['subJ']
        for w in [[f[s] for s in y] for y in ch['reps']]:
            pw = list(range(2 * W.N))
            for r in w:
                for i in range(2 * W.N):
                    pw[i] = W.reflections[r][pw[i]]
            fus.append(cycw.index(W.cycletyperoots(tuple(pw))))
        H.fusions[W.cartanname]['classes'] = fus[:]
        sgn = [(-1)**len(w) for w in ch['reps']]
        neu = inducedchar(W, H, sgn)
        for irr in ti:
            scal = sum(sgn[c] * cl[c] * irr[fus[c]] for c in range(len(cl))) // H.order
            neu = [neu[i] - scal * irr[i] for i in range(len(neu))]
        ti.append(neu[:])
    return [ti[nn.index(i)] for i in range(len(nn))]

# F chartableD


def chartableD(n):
    r"""returns the character table of the finite Coxeter group of type
    D_n.   The rows and  columns are  indexed  by suitable pairs of
    partitions of n, as in gap-chevie.  This  is  done by taking the
    irreducible characters of  type B_n  and restricting  them to a
    reflection subgroup of type D_n. (Hence, the efficiency of this
    program heavily relies on 'chartableB'.) If n is odd,  all  the
    restrictions are irreducible. If n is even, the restrictions of
    all those characters of B_n which are labelled  (alpha, alpha),
    where  alpha is a partition of  n/2, split into two irreducible
    components;  these two components are denoted by (alpha, +) and
    (alpha, -). The notation is chosen as in Lusztig's book (4.6.2)
    (see also [Ge-Pf, 5.6.3] but note that the notation needs to be
    adjusted there, as indicated below).

    Let alpha  be a partition of n/2  and denote by alpha+alpha the
    partition of n  obtained by taking  each part of  alpha exactly
    twice. Let  H be the parabolic  subgroup  of W(D_n) (isomorphic
    to the symmetric group of degree n)  which is  generated by the
    simple reflections labelled by 1, 2, ..., n-1. Then

      Ind(chi_{alpha+alpha})=chi_{(alpha, -)} + characters with
                                               higher b-invariant,

    where Ind denotes induction from H to W(D_n).

    Note that this function  uses the following  convention for the
    embedding of W(D_n) into W(B_n)::

                      0   1   2          n-1
          B_n         o=<=o---o-- . . . --o

                   1' o
                       \    3'          (n-1)'
          D_n        2' o---o---  . . . --o
                       /
                   0' o

    where 0' -> 1, 1' -> 010, 2' -> 2, 3' -> 3, 4' -> 4, ...

    Further note the following compatibility with the corresponding
    CHEVIE-GAP table in the case where n is even:

    * If n/2 is even, then the tables (together with the labels) are
      exactly the same.
    * If n/2 is odd, then labels are the same, but in the table, all
      rows corresponding to +/- characters have to be swapped.

    >>> W = coxeter("D", 4); chartable(W)['irreducibles']
    [[3, -1, 3, -1, 1, -1, 3, -1, -1, 0, 0, -1, 1],
     [3, -1, 3, -1, 1, -1, -1, 3, -1, 0, 0, 1, -1],
     [4, 0, -4, -2, 0, 2, 0, 0, 0, 1, -1, 0, 0],
     [1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, -1],
     [6, -2, 6, 0, 0, 0, -2, -2, 2, 0, 0, 0, 0],
     [8, 0, -8, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
     [3, 3, 3, -1, -1, -1, -1, -1, -1, 0, 0, 1, 1],
     [3, -1, 3, 1, -1, 1, 3, -1, -1, 0, 0, 1, -1],
     [3, -1, 3, 1, -1, 1, -1, 3, -1, 0, 0, -1, 1],
     [2, 2, 2, 0, 0, 0, 2, 2, 2, -1, -1, 0, 0],
     [4, 0, -4, 2, 0, -2, 0, 0, 0, 1, -1, 0, 0],
     [3, 3, 3, 1, 1, 1, -1, -1, -1, 0, 0, -1, -1],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]
    >>> H = reflectionsubgroup(W, [1, 2, 3]); H.cartantype
    [['A', [0, 1, 2]]]
    >>> t = inductiontable(H, W)
    >>> t1 = transposemat(t['scalar'])
    >>> t['charH']
    [('[1, 1, 1, 1]',), ('[2, 1, 1]',), ('[2, 2]',), ('[3, 1]',), ('[4]',)]
    >>> chartable(W)['b']
    [6, 6, 7, 12, 4, 3, 6, 2, 2, 4, 1, 2, 0]
    >>> [chartable(W)['charnames'][i] for i in [0, 1, 7, 8]]
    [('[[1, 1], +]',), ('[[1, 1], -]',), ('[[2], +]',), ('[[2], -]',)]

    >>> t1[0]     # take alpha=(1, 1), position 0 in t['charH']
    [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    >>> t['charW'][1]
    ('[[1, 1], -]',)

    >>> t1[2]     # take alpha=(2), position 2 in t['charH']
    [0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0]
    >>> t['charW'][8]
    ('[[2], -]',)
    """
    W1 = coxeter("B", n)
    r1 = reflections(W1)
    W = reflectionsubgroup(W1, list(range(1, n)) +
                   [r1.index(W1.wordtoperm([0, 1, 0]))])
    if n == 2:
        suba = [0]
    else:
        suba = W.cartantype[0][1][:]   # define embedding of S_n in W
        suba.remove(0)
    cw = conjugacyclasses(W)
    cl = cw['classlengths']
    pt = partitiontuples(n, 2)
    fus = []  # faster than fusionconjugacyclasses
    for i, mu in enumerate(pt):
        if not len(mu[1]) % 2:
            if not mu[1] and all(not x % 2 for x in mu[0]):
                fus.append(i)
                fus.append(i)
            else:
                fus.append(i)
    # if fus!=fusionconjugacyclasses(W, W1):
    #  print("mist")
    #  return "mist"
    pt1 = []   # tuples relevant for D
    binv = []
    trouble = []
    ct = chartableB(n)
    ti = []   # table of restrictions
    for mu in pt:
        if sum(mu[0]) >= sum(mu[1]):
            b = (2 * sum(i * mu[0][i] for i in range(len(mu[0]))) + 2 * sum(i * mu[1][i]
                                        for i in range(len(mu[1]))) + sum(mu[1]))
        else:
            b = (2 * sum(i * mu[0][i] for i in range(len(mu[0]))) + 2 * sum(i * mu[1][i]
                                        for i in range(len(mu[1]))) + sum(mu[0]))
        if mu[0] == mu[1]:
            trouble.append([mu[0][:], b])
            pt1.append(mu)
            binv.append(b)
            ti.append([ct[pt.index(mu)][j] for j in fus])
            pt1.append(mu)
            binv.append(b)
            ti.append([ct[pt.index(mu)][j] for j in fus])
        elif mu[0] < mu[1]:
            pt1.append(mu)
            binv.append(b)
            ti.append([ct[pt.index(mu)][j] for j in fus])
    trouble.sort(reverse=True, key=(lambda t: t[1]))
    # print(W.cartantype, W.fusions)
    for t in trouble:
        J = list(range(n))
        l = 0
        for i in [2 * d for d in dualpartition(t[0])]:
            l += i
            J.remove(l - 1)
        # print(t, J, suba, [suba[j] for j in J])
        H = reflectionsubgroup(W, [suba[j] for j in J])
        neu = inducedchar(W, H, [(-1)**len(w)
                        for w in conjugacyclasses(H)['reps']])
        for i in range(len(cl)):
            if binv[i] > t[1]:
                scal = sum(cl[k] * ti[i][k] * neu[k] for k in range(len(cl))
                           if neu[k] != 0) // W.order
                for k in range(len(cl)):
                    neu[k] -= scal * ti[i][k]
        i = pt1.index([t[0], t[0]])
        ti[i + 1] = [neu[j] for j in range(len(cl))]
        ti[i] = [ti[i][j] - neu[j] for j in range(len(cl))]
    return ti

# F irrchardata


def irrchardata(typ, n, chars=True):
    """returns the irreducible characters of the finite Coxeter
    group of  type 'typ' and  rank 'n'.  The data  are taken
    from the corresponding files in gap-chevie.

    See also 'chartable, 'chartablesymmetric', 'chartableB',
    'chartableD'.
    """
    ti = [[False]]
    if typ[0] == 'A' and n == 0:
        if chars:
            ti = [[1]]
        nam = ['1']
        binv = [0]
        ainv = [0]
    if typ[0] == 'A' and n >= 1:
        if chars:
            ti = chartablesymmetric(n + 1)
        binv, nam = [], []
        for mu in partitions(n + 1):
            binv.append(sum(i * mu[i] for i in range(len(mu))))
            nam.append(str(mu))
        ainv = binv[:]
    if typ[0] == 'B' or typ[0] == 'C':
        if chars:
            ti = chartableB(n)
        binv, ainv, nam = [], [], []
        for mu in partitiontuples(n, 2):
            binv.append(2 * sum(i * mu[0][i] for i in range(len(mu[0])))
                    + 2 * sum(i * mu[1][i] for i in range(len(mu[1]))) + sum(mu[1]))
            ainv.append(ainvbipartition(n, 1, 1, mu))
            nam.append(str(mu))
    if typ[0] == 'D':
        if chars:
            ti = chartableD(n)
        binv, ainv, nam = [], [], []
        for mu in partitiontuples(n, 2):
            if sum(mu[0]) >= sum(mu[1]):
                b = (2 * sum(i * mu[0][i] for i in range(len(mu[0]))) + 2 * sum(i * mu[1][i]
                                            for i in range(len(mu[1]))) + sum(mu[1]))
            else:
                b = (2 * sum(i * mu[0][i] for i in range(len(mu[0]))) + 2 * sum(i * mu[1][i]
                                            for i in range(len(mu[1]))) + sum(mu[0]))
            if mu[0] == mu[1]:
                binv.append(b)
                ainv.append(ainvbipartition(n, 1, 0, mu))
                nam.append('[' + str(mu[0]) + ', +]')
                binv.append(b)
                ainv.append(ainvbipartition(n, 1, 0, mu))
                nam.append('[' + str(mu[1]) + ', -]')
            elif mu[0] < mu[1]:
                binv.append(b)
                ainv.append(ainvbipartition(n, 1, 0, mu))
                nam.append(str(mu))
    if typ[0] == 'G':
        if chars:
            ti = [[1, 1, 1, 1, 1, 1], [1, -1, -1, 1, 1, 1], [1, 1, -1, -1, 1, -1],
                [1, -1, 1, -1, 1, -1], [2, 0, 0, 1, -1, -2], [2, 0, 0, -1, -1, 2]]
        binv = [0, 6, 3, 3, 1, 2]
        ainv = [0, 6, 1, 1, 1, 1]
        nam = ["phi_{1, 0}", "phi_{1, 6}", "phi_{1, 3}'", "phi_{1, 3}''",
                                           "phi_{2, 1}", "phi_{2, 2}"]
    if typ[0] == 'F':
        if chars:
            ti = [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
                [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, -1, -1, -1, -1],
                [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1],
                [2, 2, 2, 2, 2, 2, -1, -1, -1, -1, -1, 2, 2, -1, -1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [2, 2, 2, 2, 2, 2, -1, -1, -1, -1, -1, -2, -2, 1, 1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [2, 2, 2, -1, -1, 2, 2, 2, -1, -1, -1, 0, 0, 0, 0, 0, 2, 2, -1, -1, 2, 0, 0, 0, 0],
                [2, 2, 2, -1, -1, 2, 2, 2, -1, -1, -1, 0, 0, 0, 0, 0, -2, -2, 1, 1, -2, 0, 0, 0, 0],
                [4, 4, 4, -2, -2, 4, -2, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [9, 9, 1, 0, 0, -3, 0, 0, 0, 0, 0, 3, 3, 0, 0, -1, 3, 3, 0, 0, -1, 1, 1, 1, -1],
                [9, 9, 1, 0, 0, -3, 0, 0, 0, 0, 0, 3, 3, 0, 0, -1, -3, -3, 0, 0, 1, -1, -1, -1, 1],
                [9, 9, 1, 0, 0, -3, 0, 0, 0, 0, 0, -3, -3, 0, 0, 1, 3, 3, 0, 0, -1, -1, -1, -1, 1],
                [9, 9, 1, 0, 0, -3, 0, 0, 0, 0, 0, -3, -3, 0, 0, 1, -3, -3, 0, 0, 1, 1, 1, 1, -1],
                [6, 6, -2, 0, 0, 2, 0, 0, 3, 3, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, 0],
                [6, 6, -2, 0, 0, 2, 0, 0, 3, 3, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 0],
                [12, 12, -4, 0, 0, 4, 0, 0, -3, -3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [4, -4, 0, 1, -1, 0, 1, -1, -2, 2, 0, 2, -2, -1, 1, 0, 2, -2, -1, 1, 0, 0, 2, -2, 0],
                [4, -4, 0, 1, -1, 0, 1, -1, -2, 2, 0, 2, -2, -1, 1, 0, -2, 2, 1, -1, 0, 0, -2, 2, 0],
                [4, -4, 0, 1, -1, 0, 1, -1, -2, 2, 0, -2, 2, 1, -1, 0, 2, -2, -1, 1, 0, 0, -2, 2, 0],
                [4, -4, 0, 1, -1, 0, 1, -1, -2, 2, 0, -2, 2, 1, -1, 0, -2, 2, 1, -1, 0, 0, 2, -2, 0],
                [8, -8, 0, 2, -2, 0, -1, 1, 2, -2, 0, 4, -4, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [8, -8, 0, 2, -2, 0, -1, 1, 2, -2, 0, -4, 4, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [8, -8, 0, -1, 1, 0, 2, -2, 2, -2, 0, 0, 0, 0, 0, 0, 4, -4, 1, -1, 0, 0, 0, 0, 0],
                [8, -8, 0, -1, 1, 0, 2, -2, 2, -2, 0, 0, 0, 0, 0, 0, -4, 4, -1, 1, 0, 0, 0, 0, 0],
                [16, -16, 0, -2, 2, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
        binv = [0, 12, 12, 24, 4, 16, 4, 16, 8, 2, 6, 6, 10, 6, 6, 4, 1, 7, 7, 13, 3, 9, 3, 9, 5]
        ainv = [0, 4, 4, 24, 1, 13, 1, 13, 4, 2, 4, 4, 10, 4, 4, 4, 1, 4, 4, 13, 3, 9, 3, 9, 4]
        nam = ["1_1", "1_2", "1_3", "1_4", "2_1", "2_2", "2_3", "2_4", "4_1", "9_1",
              "9_2", "9_3", "9_4", "6_1", "6_2", "12", "4_2", "4_3", "4_4", "4_5",
              "8_1", "8_2", "8_3", "8_4", "16"]
    if typ[0] == 'E' and n == 6:
        if chars:
            ti = [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
                [10, -6, 2, 1, -2, 4, 2, -2, 0, -3, 0, 0, 2, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [6, -2, 2, -3, 3, 0, 2, 0, 1, 1, 1, -2, -1, 0, -1, 4, 0, -2, 2, 1, -2, 0, 0, -1, 1],
                [6, -2, 2, -3, 3, 0, 2, 0, 1, 1, 1, -2, -1, 0, -1, -4, 0, 2, -2, -1, 2, 0, 0, 1, -1],
                [20, 4, -4, -7, 2, 2, 4, 0, 0, 1, -2, -2, 2, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [15, -1, -1, 6, 3, 0, 3, -1, 0, 2, -1, 2, -1, 0, 0, 5, -3, 1, 1, -1, 2, 0, -1, 0, 1],
                [15, -1, -1, 6, 3, 0, 3, -1, 0, 2, -1, 2, -1, 0, 0, -5, 3, -1, -1, 1, -2, 0, 1, 0, -1],
                [15, 7, 3, -3, 0, 3, -1, 1, 0, 1, -2, 1, 0, 0, -1, 5, 1, 3, -1, 2, -1, 1, -1, 0, 0],
                [15, 7, 3, -3, 0, 3, -1, 1, 0, 1, -2, 1, 0, 0, -1, -5, -1, -3, 1, -2, 1, -1, 1, 0, 0],
                [20, 4, 4, 2, 5, -1, 0, 0, 0, -2, 1, 1, 1, -1, 0, 10, 2, 2, 2, 1, 1, -1, 0, 0, -1],
                [20, 4, 4, 2, 5, -1, 0, 0, 0, -2, 1, 1, 1, -1, 0, -10, -2, -2, -2, -1, -1, 1, 0, 0, 1],
                [24, 8, 0, 6, 0, 3, 0, 0, -1, 2, 2, -1, 0, 0, 0, 4, 4, 0, 0, -2, 1, 1, 0, -1, 0],
                [24, 8, 0, 6, 0, 3, 0, 0, -1, 2, 2, -1, 0, 0, 0, -4, -4, 0, 0, 2, -1, -1, 0, 1, 0],
                [30, -10, 2, 3, 3, 3, -2, 0, 0, -1, -1, -1, -1, 0, 1, 10, -2, -4, 0, 1, 1, 1, 0, 0, -1],
                [30, -10, 2, 3, 3, 3, -2, 0, 0, -1, -1, -1, -1, 0, 1, -10, 2, 4, 0, -1, -1, -1, 0, 0, 1],
                [60, 12, 4, -3, -6, 0, 4, 0, 0, -3, 0, 0, -2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [80, -16, 0, -10, -4, 2, 0, 0, 0, 2, 2, 2, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [90, -6, -6, 9, 0, 0, 2, 2, 0, -3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [60, -4, 4, 6, -3, -3, 0, 0, 0, 2, -1, -1, 1, 0, 0, 10, 2, -2, -2, 1, 1, -1, 0, 0, 1],
                [60, -4, 4, 6, -3, -3, 0, 0, 0, 2, -1, -1, 1, 0, 0, -10, -2, 2, 2, -1, -1, 1, 0, 0, -1],
                [64, 0, 0, -8, 4, -2, 0, 0, -1, 0, 0, 0, 0, 1, 0, 16, 0, 0, 0, -2, -2, 0, 0, 1, 0],
                [64, 0, 0, -8, 4, -2, 0, 0, -1, 0, 0, 0, 0, 1, 0, -16, 0, 0, 0, 2, 2, 0, 0, -1, 0],
                [81, 9, -3, 0, 0, 0, -3, -1, 1, 0, 0, 0, 0, 0, 0, 9, -3, 3, -1, 0, 0, 0, 1, -1, 0],
                [81, 9, -3, 0, 0, 0, -3, -1, 1, 0, 0, 0, 0, 0, 0, -9, 3, -3, 1, 0, 0, 0, -1, 1, 0]]
        binv = [0, 36, 9, 1, 25, 10, 5, 17, 4, 16, 2, 20, 6, 12, 3, 15, 8, 7, 8, 5, 11, 4, 13, 6, 10]
        ainv = [0, 36, 7, 1, 25, 7, 3, 15, 3, 15, 2, 20, 6, 12, 3, 15, 7, 7, 7, 5, 11, 4, 13, 6, 10]
        nam = ["1_p", "1_p'", "10_s", "6_p", "6_p'", "20_s", "15_p", "15_p'", "15_q",
             "15_q'", "20_p", "20_p'", "24_p", "24_p'", "30_p", "30_p'", "60_s",
             "80_s", "90_s", "60_p", "60_p'", "64_p", "64_p'", "81_p", "81_p'"]
    if typ[0] == 'E' and n == 7:
        if chars:
            ti = [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1,
                 -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                 -1, -1, -1, -1, -1, -1, -1],
                [7, -5, -1, 3, -1, 4, -2, 1, 3, 1, -3, -1, 1, 2, -2, 2, 2, 0, 1, -1, -1, 0, -1, 1, 1, 0,
                 -2, 0, 0, -1, 7, -5, -1, 3, -1, 4, -2, 1, 3, 1, -3, -1, 1, 2, -2, 2, 2, 0, 1, -1, -1, 0, -1,
                 1, 1, 0, -2, 0, 0, -1],
                [7, -5, -1, 3, -1, 4, -2, 1, 3, 1, -3, -1, 1, 2, -2, 2, 2, 0, 1, -1, -1, 0, -1, 1, 1, 0,
                 -2, 0, 0, -1, -7, 5, 1, -3, 1, -4, 2, -1, -3, -1, 3, 1, -1, -2, 2, -2, -2, 0, -1, 1, 1, 0, 1,
                 -1, -1, 0, 2, 0, 0, 1],
                [15, -5, 7, 3, -1, 0, -3, 3, -1, -3, 1, 3, 1, 0, -2, -2, 1, 0, 1, 1, -1, 1, 1, -1, 0, 0, 0,
                 -2, -1, 0, 15, -5, 7, 3, -1, 0, -3, 3, -1, -3, 1, 3, 1, 0, -2, -2, 1, 0, 1, 1, -1, 1, 1, -1,
                 0, 0, 0, -2, -1, 0],
                [15, -5, 7, 3, -1, 0, -3, 3, -1, -3, 1, 3, 1, 0, -2, -2, 1, 0, 1, 1, -1, 1, 1, -1, 0, 0, 0,
                 -2, -1, 0, -15, 5, -7, -3, 1, 0, 3, -3, 1, 3, -1, -3, -1, 0, 2, 2, -1, 0, -1, -1, 1, -1, -1,
                 1, 0, 0, 0, 2, 1, 0],
                [21, 9, -3, 1, -3, 6, 3, 0, 5, -1, 3, 1, -1, 1, 0, 0, 3, -2, 0, 0, 0, 0, -1, 1, 0, -1, 2, 0,
                 -1, 1, 21, 9, -3, 1, -3, 6, 3, 0, 5, -1, 3, 1, -1, 1, 0, 0, 3, -2, 0, 0, 0, 0, -1, 1, 0, -1, 2,
                 0, -1, 1],
                [21, 9, -3, 1, -3, 6, 3, 0, 5, -1, 3, 1, -1, 1, 0, 0, 3, -2, 0, 0, 0, 0, -1, 1, 0, -1, 2, 0,
                 -1, 1, -21, -9, 3, -1, 3, -6, -3, 0, -5, 1, -3, -1, 1, -1, 0, 0, -3, 2, 0, 0, 0, 0, 1, -1, 0,
                 1, -2, 0, 1, -1],
                [21, -11, 5, 5, -3, 6, 3, 0, 1, -3, -3, 1, 1, 1, -2, 2, -1, 2, -2, 2, 0, 0, -1, -1, 0, -1,
                 0, 0, 1, 1, 21, -11, 5, 5, -3, 6, 3, 0, 1, -3, -3, 1, 1, 1, -2, 2, -1, 2, -2, 2, 0, 0, -1,
                 -1, 0, -1, 0, 0, 1, 1],
                [21, -11, 5, 5, -3, 6, 3, 0, 1, -3, -3, 1, 1, 1, -2, 2, -1, 2, -2, 2, 0, 0, -1, -1, 0, -1,
                 0, 0, 1, 1, -21, 11, -5, -5, 3, -6, -3, 0, -1, 3, 3, -1, -1, -1, 2, -2, 1, -2, 2, -2, 0, 0,
                 1, 1, 0, 1, 0, 0, -1, -1],
                [27, 15, 3, 7, 3, 9, 0, 0, 3, 1, 5, -1, 1, 2, 3, 3, 0, 1, 0, 0, 0, -1, 1, -1, 0, 0, 1, -1, 0,
                 -1, 27, 15, 3, 7, 3, 9, 0, 0, 3, 1, 5, -1, 1, 2, 3, 3, 0, 1, 0, 0, 0, -1, 1, -1, 0, 0, 1, -1, 0,
                 -1],
                [27, 15, 3, 7, 3, 9, 0, 0, 3, 1, 5, -1, 1, 2, 3, 3, 0, 1, 0, 0, 0, -1, 1, -1, 0, 0, 1, -1, 0,
                 -1, -27, -15, -3, -7, -3, -9, 0, 0, -3, -1, -5, 1, -1, -2, -3, -3, 0, -1, 0, 0, 0, 1, -1,
                 1, 0, 0, -1, 1, 0, 1],
                [35, -5, 3, -5, 3, 5, -1, 2, 7, -1, -1, -1, -1, 0, 1, -3, 3, 1, -2, 0, 0, 0, 1, 1, -1, 0,
                 -1, -1, 1, 0, 35, -5, 3, -5, 3, 5, -1, 2, 7, -1, -1, -1, -1, 0, 1, -3, 3, 1, -2, 0, 0, 0, 1,
                 1, -1, 0, -1, -1, 1, 0],
                [35, -5, 3, -5, 3, 5, -1, 2, 7, -1, -1, -1, -1, 0, 1, -3, 3, 1, -2, 0, 0, 0, 1, 1, -1, 0,
                 -1, -1, 1, 0, -35, 5, -3, 5, -3, -5, 1, -2, -7, 1, 1, 1, 1, 0, -1, 3, -3, -1, 2, 0, 0, 0, -1,
                 -1, 1, 0, 1, 1, -1, 0],
                [35, 15, 11, 7, 3, 5, -1, 2, -1, 5, 1, 3, 1, 0, 3, -1, -1, 1, 0, 2, 0, 0, -1, 1, -1, 0, -1,
                 1, -1, 0, 35, 15, 11, 7, 3, 5, -1, 2, -1, 5, 1, 3, 1, 0, 3, -1, -1, 1, 0, 2, 0, 0, -1, 1, -1,
                 0, -1, 1, -1, 0],
                [35, 15, 11, 7, 3, 5, -1, 2, -1, 5, 1, 3, 1, 0, 3, -1, -1, 1, 0, 2, 0, 0, -1, 1, -1, 0, -1,
                 1, -1, 0, -35, -15, -11, -7, -3, -5, 1, -2, 1, -5, -1, -3, -1, 0, -3, 1, 1, -1, 0, -2, 0,
                 0, 1, -1, 1, 0, 1, -1, 1, 0],
                [56, -24, -8, 8, 0, 11, 2, 2, 0, 4, -4, 0, 0, 1, -3, 1, -2, -1, 0, -2, 0, 0, 0, 0, -1, 1,
                 1, -1, 0, 1, 56, -24, -8, 8, 0, 11, 2, 2, 0, 4, -4, 0, 0, 1, -3, 1, -2, -1, 0, -2, 0, 0, 0,
                 0, -1, 1, 1, -1, 0, 1],
                [56, -24, -8, 8, 0, 11, 2, 2, 0, 4, -4, 0, 0, 1, -3, 1, -2, -1, 0, -2, 0, 0, 0, 0, -1, 1,
                 1, -1, 0, 1, -56, 24, 8, -8, 0, -11, -2, -2, 0, -4, 4, 0, 0, -1, 3, -1, 2, 1, 0, 2, 0, 0, 0,
                 0, 1, -1, -1, 1, 0, -1],
                [70, -10, -10, 6, -2, -5, 7, 1, 2, 2, 2, 2, -2, 0, -1, -1, -1, 3, -1, -1, 1, 0, 0, 0, 1,
                 0, -1, -1, -1, 0, 70, -10, -10, 6, -2, -5, 7, 1, 2, 2, 2, 2, -2, 0, -1, -1, -1, 3, -1, -1,
                 1, 0, 0, 0, 1, 0, -1, -1, -1, 0],
                [70, -10, -10, 6, -2, -5, 7, 1, 2, 2, 2, 2, -2, 0, -1, -1, -1, 3, -1, -1, 1, 0, 0, 0, 1,
                 0, -1, -1, -1, 0, -70, 10, 10, -6, 2, 5, -7, -1, -2, -2, -2, -2, 2, 0, 1, 1, 1, -3, 1, 1,
                 -1, 0, 0, 0, -1, 0, 1, 1, 1, 0],
                [84, 4, 20, 4, 4, -6, 3, 3, 4, 0, 0, 4, 0, -1, -2, 2, -1, -2, 1, -1, 1, 0, 0, 0, 0, -1, 0,
                 0, 1, -1, 84, 4, 20, 4, 4, -6, 3, 3, 4, 0, 0, 4, 0, -1, -2, 2, -1, -2, 1, -1, 1, 0, 0, 0, 0,
                 -1, 0, 0, 1, -1],
                [84, 4, 20, 4, 4, -6, 3, 3, 4, 0, 0, 4, 0, -1, -2, 2, -1, -2, 1, -1, 1, 0, 0, 0, 0, -1, 0,
                 0, 1, -1, -84, -4, -20, -4, -4, 6, -3, -3, -4, 0, 0, -4, 0, 1, 2, -2, 1, 2, -1, 1, -1, 0,
                 0, 0, 0, 1, 0, 0, -1, 1],
                [105, -35, 1, 5, 1, 15, -3, -3, 5, -1, -5, 1, -1, 0, 1, 1, 1, -1, 1, 1, 1, 0, 1, -1, 0, 0,
                 -1, 1, -1, 0, 105, -35, 1, 5, 1, 15, -3, -3, 5, -1, -5, 1, -1, 0, 1, 1, 1, -1, 1, 1, 1, 0, 1,
                 -1, 0, 0, -1, 1, -1, 0],
                [105, -35, 1, 5, 1, 15, -3, -3, 5, -1, -5, 1, -1, 0, 1, 1, 1, -1, 1, 1, 1, 0, 1, -1, 0, 0,
                 -1, 1, -1, 0, -105, 35, -1, -5, -1, -15, 3, 3, -5, 1, 5, -1, 1, 0, -1, -1, -1, 1, -1, -1,
                 -1, 0, -1, 1, 0, 0, 1, -1, 1, 0],
                [105, 25, -7, 9, 1, 0, 6, 3, -3, -3, -3, -3, 1, 0, 4, -4, 2, 0, 1, -1, 1, 0, -1, -1, 0, 0,
                 0, 0, 0, 0, 105, 25, -7, 9, 1, 0, 6, 3, -3, -3, -3, -3, 1, 0, 4, -4, 2, 0, 1, -1, 1, 0, -1,
                 -1, 0, 0, 0, 0, 0, 0],
                [105, 25, -7, 9, 1, 0, 6, 3, -3, -3, -3, -3, 1, 0, 4, -4, 2, 0, 1, -1, 1, 0, -1, -1, 0, 0,
                 0, 0, 0, 0, -105, -25, 7, -9, -1, 0, -6, -3, 3, 3, 3, 3, -1, 0, -4, 4, -2, 0, -1, 1, -1, 0,
                 1, 1, 0, 0, 0, 0, 0, 0],
                [105, 5, 17, -3, -7, 0, 6, 3, -3, 3, -1, 1, -1, 0, 2, 2, 2, 0, -1, -1, -1, 0, 1, -1, 0, 0,
                 0, 2, 0, 0, 105, 5, 17, -3, -7, 0, 6, 3, -3, 3, -1, 1, -1, 0, 2, 2, 2, 0, -1, -1, -1, 0, 1,
                 -1, 0, 0, 0, 2, 0, 0],
                [105, 5, 17, -3, -7, 0, 6, 3, -3, 3, -1, 1, -1, 0, 2, 2, 2, 0, -1, -1, -1, 0, 1, -1, 0, 0,
                 0, 2, 0, 0, -105, -5, -17, 3, 7, 0, -6, -3, 3, -3, 1, -1, 1, 0, -2, -2, -2, 0, 1, 1, 1, 0,
                 -1, 1, 0, 0, 0, -2, 0, 0],
                [120, 40, -8, 8, 0, 15, -6, 0, 0, -4, 4, 0, 0, 0, 1, 1, -2, -1, -2, -2, 0, 1, 0, 0, 0, 0,
                 -1, 1, 0, 0, 120, 40, -8, 8, 0, 15, -6, 0, 0, -4, 4, 0, 0, 0, 1, 1, -2, -1, -2, -2, 0, 1, 0,
                 0, 0, 0, -1, 1, 0, 0],
                [120, 40, -8, 8, 0, 15, -6, 0, 0, -4, 4, 0, 0, 0, 1, 1, -2, -1, -2, -2, 0, 1, 0, 0, 0, 0,
                 -1, 1, 0, 0, -120, -40, 8, -8, 0, -15, 6, 0, 0, 4, -4, 0, 0, 0, -1, -1, 2, 1, 2, 2, 0, -1, 0,
                 0, 0, 0, 1, -1, 0, 0],
                [168, 40, 8, 8, 8, 6, 6, -3, 0, 0, 0, 0, 0, -2, -2, 2, 2, 2, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0,
                 0, 1, 168, 40, 8, 8, 8, 6, 6, -3, 0, 0, 0, 0, 0, -2, -2, 2, 2, 2, 1, -1, -1, 0, 0, 0, 0, 0, 0,
                 0, 0, 1],
                [168, 40, 8, 8, 8, 6, 6, -3, 0, 0, 0, 0, 0, -2, -2, 2, 2, 2, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0,
                 0, 1, -168, -40, -8, -8, -8, -6, -6, 3, 0, 0, 0, 0, 0, 2, 2, -2, -2, -2, -1, 1, 1, 0, 0, 0,
                 0, 0, 0, 0, 0, -1],
                [189, 21, -3, -11, -3, 9, 0, 0, 9, 1, 1, 1, 1, -1, -3, -3, 0, 1, 0, 0, 0, 0, -1, -1, 0, 1,
                 1, 1, 0, -1, 189, 21, -3, -11, -3, 9, 0, 0, 9, 1, 1, 1, 1, -1, -3, -3, 0, 1, 0, 0, 0, 0, -1,
                 -1, 0, 1, 1, 1, 0, -1],
                [189, 21, -3, -11, -3, 9, 0, 0, 9, 1, 1, 1, 1, -1, -3, -3, 0, 1, 0, 0, 0, 0, -1, -1, 0, 1,
                 1, 1, 0, -1, -189, -21, 3, 11, 3, -9, 0, 0, -9, -1, -1, -1, -1, 1, 3, 3, 0, -1, 0, 0, 0, 0,
                 1, 1, 0, -1, -1, -1, 0, 1],
                [189, -51, -3, 13, -3, 9, 0, 0, -3, 1, 1, -3, 1, -1, -3, -3, 0, 1, 0, 0, 0, 0, 1, 1, 0,
                 -1, 1, 1, 0, -1, 189, -51, -3, 13, -3, 9, 0, 0, -3, 1, 1, -3, 1, -1, -3, -3, 0, 1, 0, 0, 0,
                 0, 1, 1, 0, -1, 1, 1, 0, -1],
                [189, -51, -3, 13, -3, 9, 0, 0, -3, 1, 1, -3, 1, -1, -3, -3, 0, 1, 0, 0, 0, 0, 1, 1, 0,
                 -1, 1, 1, 0, -1, -189, 51, 3, -13, 3, -9, 0, 0, 3, -1, -1, 3, -1, 1, 3, 3, 0, -1, 0, 0, 0, 0,
                 -1, -1, 0, 1, -1, -1, 0, 1],
                [189, -39, 21, 1, -3, 9, 0, 0, -3, -5, -1, 1, -1, -1, 3, 3, 0, 1, 0, 0, 0, 0, -1, 1, 0, 1,
                 1, -1, 0, -1, 189, -39, 21, 1, -3, 9, 0, 0, -3, -5, -1, 1, -1, -1, 3, 3, 0, 1, 0, 0, 0, 0,
                 -1, 1, 0, 1, 1, -1, 0, -1],
                [189, -39, 21, 1, -3, 9, 0, 0, -3, -5, -1, 1, -1, -1, 3, 3, 0, 1, 0, 0, 0, 0, -1, 1, 0, 1,
                 1, -1, 0, -1, -189, 39, -21, -1, 3, -9, 0, 0, 3, 5, 1, -1, 1, 1, -3, -3, 0, -1, 0, 0, 0, 0,
                 1, -1, 0, -1, -1, 1, 0, 1],
                [210, 50, 2, 2, -6, 15, 3, 0, -2, 2, 2, -2, -2, 0, -1, -1, -1, -1, 2, 2, 0, 0, 0, 0, 0, 0,
                 -1, -1, 1, 0, 210, 50, 2, 2, -6, 15, 3, 0, -2, 2, 2, -2, -2, 0, -1, -1, -1, -1, 2, 2, 0, 0,
                 0, 0, 0, 0, -1, -1, 1, 0],
                [210, 50, 2, 2, -6, 15, 3, 0, -2, 2, 2, -2, -2, 0, -1, -1, -1, -1, 2, 2, 0, 0, 0, 0, 0, 0,
                 -1, -1, 1, 0, -210, -50, -2, -2, 6, -15, -3, 0, 2, -2, -2, 2, 2, 0, 1, 1, 1, 1, -2, -2, 0,
                 0, 0, 0, 0, 0, 1, 1, -1, 0],
                [210, 10, -14, 10, 2, -15, -6, 3, 6, -2, -2, -2, -2, 0, 1, 1, -2, 1, 1, 1, -1, 0, 0, 0,
                 0, 0, 1, 1, 0, 0, 210, 10, -14, 10, 2, -15, -6, 3, 6, -2, -2, -2, -2, 0, 1, 1, -2, 1, 1, 1,
                 -1, 0, 0, 0, 0, 0, 1, 1, 0, 0],
                [210, 10, -14, 10, 2, -15, -6, 3, 6, -2, -2, -2, -2, 0, 1, 1, -2, 1, 1, 1, -1, 0, 0, 0,
                 0, 0, 1, 1, 0, 0, -210, -10, 14, -10, -2, 15, 6, -3, -6, 2, 2, 2, 2, 0, -1, -1, 2, -1, -1,
                 -1, 1, 0, 0, 0, 0, 0, -1, -1, 0, 0],
                [216, -24, 24, 8, 0, -9, 0, 0, 0, -4, 4, 0, 0, 1, -3, -3, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1,
                 -1, 1, 0, 1, 216, -24, 24, 8, 0, -9, 0, 0, 0, -4, 4, 0, 0, 1, -3, -3, 0, -1, 0, 0, 0, -1, 0,
                 0, 0, 1, -1, 1, 0, 1],
                [216, -24, 24, 8, 0, -9, 0, 0, 0, -4, 4, 0, 0, 1, -3, -3, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1,
                 -1, 1, 0, 1, -216, 24, -24, -8, 0, 9, 0, 0, 0, 4, -4, 0, 0, -1, 3, 3, 0, 1, 0, 0, 0, 1, 0, 0,
                 0, -1, 1, -1, 0, -1],
                [280, -40, -8, -8, 8, 10, 10, 1, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -1, 1, -1, 0, 0, 0, 1,
                 0, 0, 0, 0, 0, 280, -40, -8, -8, 8, 10, 10, 1, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -1, 1, -1,
                 0, 0, 0, 1, 0, 0, 0, 0, 0],
                [280, -40, -8, -8, 8, 10, 10, 1, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -1, 1, -1, 0, 0, 0, 1,
                 0, 0, 0, 0, 0, -280, 40, 8, 8, -8, -10, -10, -1, 0, 0, 0, 0, 0, 0, -2, 2, 2, 2, 1, -1, 1, 0,
                 0, 0, -1, 0, 0, 0, 0, 0],
                [280, 40, 24, 8, 0, -5, -8, -2, 0, 4, -4, 0, 0, 0, 1, -3, 0, -1, -2, 0, 0, 0, 0, 0, 1, 0,
                 1, -1, 0, 0, 280, 40, 24, 8, 0, -5, -8, -2, 0, 4, -4, 0, 0, 0, 1, -3, 0, -1, -2, 0, 0, 0, 0,
                 0, 1, 0, 1, -1, 0, 0],
                [280, 40, 24, 8, 0, -5, -8, -2, 0, 4, -4, 0, 0, 0, 1, -3, 0, -1, -2, 0, 0, 0, 0, 0, 1, 0,
                 1, -1, 0, 0, -280, -40, -24, -8, 0, 5, 8, 2, 0, -4, 4, 0, 0, 0, -1, 3, 0, 1, 2, 0, 0, 0, 0,
                 0, -1, 0, -1, 1, 0, 0],
                [315, -45, -21, 3, 3, 0, -9, 0, -5, 3, 3, 3, -1, 0, 0, 0, 3, 0, 0, 0, 0, 0, -1, -1, 0, 0,
                 0, 0, 1, 0, 315, -45, -21, 3, 3, 0, -9, 0, -5, 3, 3, 3, -1, 0, 0, 0, 3, 0, 0, 0, 0, 0, -1,
                 -1, 0, 0, 0, 0, 1, 0],
                [315, -45, -21, 3, 3, 0, -9, 0, -5, 3, 3, 3, -1, 0, 0, 0, 3, 0, 0, 0, 0, 0, -1, -1, 0, 0,
                 0, 0, 1, 0, -315, 45, 21, -3, -3, 0, 9, 0, 5, -3, -3, -3, 1, 0, 0, 0, -3, 0, 0, 0, 0, 0, 1,
                 1, 0, 0, 0, 0, -1, 0],
                [336, -16, 16, -16, 0, 6, -6, 0, 0, 0, 0, 0, 0, 1, 2, -2, -2, 2, 2, -2, 0, 0, 0, 0, 0, -1,
                 0, 0, 0, 1, 336, -16, 16, -16, 0, 6, -6, 0, 0, 0, 0, 0, 0, 1, 2, -2, -2, 2, 2, -2, 0, 0, 0,
                 0, 0, -1, 0, 0, 0, 1],
                [336, -16, 16, -16, 0, 6, -6, 0, 0, 0, 0, 0, 0, 1, 2, -2, -2, 2, 2, -2, 0, 0, 0, 0, 0, -1,
                 0, 0, 0, 1, -336, 16, -16, 16, 0, -6, 6, 0, 0, 0, 0, 0, 0, -1, -2, 2, 2, -2, -2, 2, 0, 0, 0,
                 0, 0, 1, 0, 0, 0, -1],
                [378, -30, -6, 2, -6, -9, 0, 0, 6, 2, 2, -2, 2, -2, 3, 3, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0,
                 -1, -1, 0, 1, 378, -30, -6, 2, -6, -9, 0, 0, 6, 2, 2, -2, 2, -2, 3, 3, 0, -1, 0, 0, 0, 0, 0,
                 0, 0, 0, -1, -1, 0, 1],
                [378, -30, -6, 2, -6, -9, 0, 0, 6, 2, 2, -2, 2, -2, 3, 3, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0,
                 -1, -1, 0, 1, -378, 30, 6, -2, 6, 9, 0, 0, -6, -2, -2, 2, -2, 2, -3, -3, 0, 1, 0, 0, 0, 0, 0,
                 0, 0, 0, 1, 1, 0, -1],
                [405, 45, -27, -3, -3, 0, 0, 0, -3, -3, -3, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 0, 0,
                 0, 0, 0, 0, 405, 45, -27, -3, -3, 0, 0, 0, -3, -3, -3, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
                 1, 0, 0, 0, 0, 0, 0],
                [405, 45, -27, -3, -3, 0, 0, 0, -3, -3, -3, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 0, 0,
                 0, 0, 0, 0, -405, -45, 27, 3, 3, 0, 0, 0, 3, 3, 3, -5, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1,
                 0, 0, 0, 0, 0, 0],
                [420, 20, 4, -12, 4, 0, -3, 3, -4, 0, 0, -4, 0, 0, -4, 4, 1, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0,
                 0, -1, 0, 420, 20, 4, -12, 4, 0, -3, 3, -4, 0, 0, -4, 0, 0, -4, 4, 1, 0, -1, 1, 1, 0, 0, 0,
                 0, 0, 0, 0, -1, 0],
                [420, 20, 4, -12, 4, 0, -3, 3, -4, 0, 0, -4, 0, 0, -4, 4, 1, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0,
                 0, -1, 0, -420, -20, -4, 12, -4, 0, 3, -3, 4, 0, 0, 4, 0, 0, 4, -4, -1, 0, 1, -1, -1, 0, 0,
                 0, 0, 0, 0, 0, 1, 0],
                [512, 0, 0, 0, 0, -16, 8, -4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0,
                 -1, 512, 0, 0, 0, 0, -16, 8, -4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0,
                 -1],
                [512, 0, 0, 0, 0, -16, 8, -4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0,
                 -1, -512, 0, 0, 0, 0, 16, -8, 4, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0,
                 0, 1]]
        binv = [0, 63, 46, 1, 28, 7, 6, 33, 36, 3, 2, 37, 22, 13, 4, 31, 30, 3, 18, 9, 12, 15, 26, 5,
              6, 21, 12, 15, 4, 25, 6, 21, 10, 17, 22, 5, 20, 7, 6, 21, 10, 13, 16, 9, 18, 9, 8, 17,
              16, 7, 14, 11, 14, 9, 8, 15, 10, 13, 12, 11]
        ainv = [0, 63, 46, 1, 25, 4, 3, 30, 36, 3, 2, 37, 16, 7, 3, 30, 30, 3, 16, 7, 10, 13, 25, 4, 6,
              21, 12, 15, 4, 25, 6, 21, 8, 15, 22, 5, 20, 7, 6, 21, 10, 13, 15, 8, 16, 7, 7, 16, 16,
              7, 13, 10, 14, 9, 8, 15, 10, 13, 11, 11]
        nam = ["1_a", "1_a'", "7_a", "7_a'", "15_a", "15_a'", "21_a", "21_a'", "21_b",
             "21_b'", "27_a", "27_a'", "35_a", "35_a'", "35_b", "35_b'", "56_a",
             "56_a'", "70_a", "70_a'", "84_a", "84_a'", "105_a", "105_a'", "105_b",
             "105_b'", "105_c", "105_c'", "120_a", "120_a'", "168_a", "168_a'",
             "189_a", "189_a'", "189_b", "189_b'", "189_c", "189_c'", "210_a",
             "210_a'", "210_b", "210_b'", "216_a", "216_a'", "280_a", "280_a'",
             "280_b", "280_b'", "315_a", "315_a'", "336_a", "336_a'", "378_a",
             "378_a'", "405_a", "405_a'", "420_a", "420_a'", "512_a", "512_a'"]
    if typ[0] == 'E' and n == 8:
        if chars:
            ti = [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                 -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                 -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                 -1, -1, -1],
                [28, 28, -4, 4, 4, 4, -4, 10, 10, 10, 10, 1, 1, 1, 1, 8, 8, 0, 0, 0, 0, 0, 3, 3, 3, 3, 2, 2,
                 2, -2, -2, -2, 5, 5, -1, -1, 1, 1, 1, -1, 0, 0, -2, 2, 2, 1, 1, 1, 1, -1, -1, -1, 2, 2, 2, 2,
                 -1, -1, 0, 0, 0, 0, 0, 0, 0, 14, 14, -2, -2, 6, 6, -2, 2, 2, 2, -2, 2, 2, 5, 5, -2, -2, -1,
                 -1, 1, 1, 1, 1, 0, 0, 0, 0, -1, -1, 4, 4, 0, 0, 1, -1, -1, -1, 0, 0, -1, -1, 1, 1, 0, 0, 2, 2],
                [28, 28, -4, 4, 4, 4, -4, 10, 10, 10, 10, 1, 1, 1, 1, 8, 8, 0, 0, 0, 0, 0, 3, 3, 3, 3, 2, 2,
                 2, -2, -2, -2, 5, 5, -1, -1, 1, 1, 1, -1, 0, 0, -2, 2, 2, 1, 1, 1, 1, -1, -1, -1, 2, 2, 2, 2,
                 -1, -1, 0, 0, 0, 0, 0, 0, 0, -14, -14, 2, 2, -6, -6, 2, -2, -2, -2, 2, -2, -2, -5, -5, 2, 2,
                 1, 1, -1, -1, -1, -1, 0, 0, 0, 0, 1, 1, -4, -4, 0, 0, -1, 1, 1, 1, 0, 0, 1, 1, -1, -1, 0, 0,
                 -2, -2],
                [35, 35, 3, 11, 11, -5, 3, 14, 14, 5, 5, -1, -1, 2, 2, 7, 7, -1, 3, 3, -1, -1, 5, 5, 0, 0,
                 6, 6, -3, 2, 2, 1, 3, 3, 0, 0, 2, 2, -2, 0, 0, 0, 1, 1, 1, 2, 2, -1, -1, 1, 1, 0, -2, -2, 1, 1,
                 1, 1, 0, 0, -1, -1, -1, 0, 0, 21, 21, 5, 5, 9, 9, 1, 1, 1, -3, 1, 6, 6, 3, 3, 2, 2, 0, 0, -1,
                 -1, 2, 2, 3, 3, -1, -1, 1, 1, 4, 4, 0, 0, -2, 0, 1, 1, 0, 0, 0, 0, -1, -1, 0, 0, 1, 1],
                [35, 35, 3, 11, 11, -5, 3, 14, 14, 5, 5, -1, -1, 2, 2, 7, 7, -1, 3, 3, -1, -1, 5, 5, 0, 0,
                 6, 6, -3, 2, 2, 1, 3, 3, 0, 0, 2, 2, -2, 0, 0, 0, 1, 1, 1, 2, 2, -1, -1, 1, 1, 0, -2, -2, 1, 1,
                 1, 1, 0, 0, -1, -1, -1, 0, 0, -21, -21, -5, -5, -9, -9, -1, -1, -1, 3, -1, -6, -6, -3,
                 -3, -2, -2, 0, 0, 1, 1, -2, -2, -3, -3, 1, 1, -1, -1, -4, -4, 0, 0, 2, 0, -1, -1, 0, 0, 0, 0,
                 1, 1, 0, 0, -1, -1],
                [70, 70, 6, -10, -10, 6, 6, 10, 10, 19, 19, -2, -2, 4, 4, 14, 14, -2, -2, -2, 2, -2, 0,
                 0, 5, 5, -6, -6, 3, 2, 2, 3, 6, 6, 0, 0, -4, -4, 0, 0, 0, 0, 2, 2, 2, -2, -2, 1, 1, 0, 0, 1, 2,
                 2, -1, -1, 2, 2, -2, -2, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [50, 50, 18, 10, 10, 10, 2, 5, 5, 5, 5, -4, -4, 5, 5, -2, -2, 6, 2, 2, 2, 2, 0, 0, 0, 0,
                 -3, -3, -3, 1, 1, 1, 0, 0, 3, 3, 1, 1, 1, -1, 1, 1, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 1, 1, 1,
                 1, -2, -2, -1, -1, -1, 0, 0, 0, 0, 20, 20, 4, 4, 0, 0, 8, 0, 0, 4, 0, 5, 5, 2, 2, 1, 1, -1,
                 -1, -2, -2, 1, 1, -2, -2, 2, 0, 0, 0, -1, -1, 3, 3, -1, 1, 0, 0, -1, -1, -1, -1, 0, 0, 1, 1,
                 0, 0],
                [50, 50, 18, 10, 10, 10, 2, 5, 5, 5, 5, -4, -4, 5, 5, -2, -2, 6, 2, 2, 2, 2, 0, 0, 0, 0,
                 -3, -3, -3, 1, 1, 1, 0, 0, 3, 3, 1, 1, 1, -1, 1, 1, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 1, 1, 1,
                 1, -2, -2, -1, -1, -1, 0, 0, 0, 0, -20, -20, -4, -4, 0, 0, -8, 0, 0, -4, 0, -5, -5, -2,
                 -2, -1, -1, 1, 1, 2, 2, -1, -1, 2, 2, -2, 0, 0, 0, 1, 1, -3, -3, 1, -1, 0, 0, 1, 1, 1, 1, 0, 0,
                 -1, -1, 0, 0],
                [84, 84, 20, 20, 20, 4, 4, 21, 21, -6, -6, 3, 3, 3, 3, 4, 4, 4, 4, 4, 0, 0, 4, 4, -1, -1,
                 5, 5, 2, 5, 5, -2, -1, -1, 5, -1, -1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, -2,
                 -2, 1, 1, 1, 1, 0, 1, 1, -1, -1, 42, 42, 10, 10, 10, 10, 10, 2, 2, 2, 2, 9, 9, -3, -3, 1, 1,
                 3, 3, 1, 1, 1, 1, 2, 2, 2, 0, 2, 2, 1, 1, 1, 1, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0, -1, -1, -1,
                 -1],
                [84, 84, 20, 20, 20, 4, 4, 21, 21, -6, -6, 3, 3, 3, 3, 4, 4, 4, 4, 4, 0, 0, 4, 4, -1, -1,
                 5, 5, 2, 5, 5, -2, -1, -1, 5, -1, -1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, -2,
                 -2, 1, 1, 1, 1, 0, 1, 1, -1, -1, -42, -42, -10, -10, -10, -10, -10, -2, -2, -2, -2, -9,
                 -9, 3, 3, -1, -1, -3, -3, -1, -1, -1, -1, -2, -2, -2, 0, -2, -2, -1, -1, -1, -1, -1, 1, 1,
                 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1],
                [168, 168, 40, 8, 8, 24, 8, -12, -12, 15, 15, 6, 6, 6, 6, 8, 8, 8, 0, 0, 4, 0, -2, -2, 3,
                 3, 4, 4, 7, -4, -4, 3, -2, -2, -2, 4, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, -1, -4,
                 -4, -1, -1, 2, 2, 0, 0, 1, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [175, 175, -17, 15, 15, 15, -1, -5, -5, -5, -5, 13, 13, 4, 4, -1, -1, -1, -1, -1, -1,
                 3, 0, 0, 0, 0, -5, -5, -5, 3, 3, 3, 1, 1, -2, -2, 0, 0, 0, 2, 0, 0, -1, -1, -1, 1, 1, 1, 1, 0,
                 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 35, 35, 3, 3, -5, -5, -5, -5, -5, 3,
                 3, 5, 5, -1, -1, -3, -3, 2, 2, 3, 3, 0, 0, -1, -1, -1, 1, 0, 0, 1, 1, 1, 1, -2, 0, 1, 1, 0, 0,
                 -1, -1, 0, 0, -1, -1, 0, 0],
                [175, 175, -17, 15, 15, 15, -1, -5, -5, -5, -5, 13, 13, 4, 4, -1, -1, -1, -1, -1, -1,
                 3, 0, 0, 0, 0, -5, -5, -5, 3, 3, 3, 1, 1, -2, -2, 0, 0, 0, 2, 0, 0, -1, -1, -1, 1, 1, 1, 1, 0,
                 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, -35, -35, -3, -3, 5, 5, 5, 5, 5, -3,
                 -3, -5, -5, 1, 1, 3, 3, -2, -2, -3, -3, 0, 0, 1, 1, 1, -1, 0, 0, -1, -1, -1, -1, 2, 0, -1,
                 -1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0],
                [210, 210, -14, 26, 26, 10, 2, 39, 39, -15, -15, -6, -6, 3, 3, 6, 6, -2, 2, 2, -2, 2,
                 5, 5, 0, 0, 7, 7, 1, -1, -1, 1, -2, -2, -5, 1, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
                 0, 3, 3, -3, -3, 0, 0, -1, -1, 1, -1, -1, 0, 0, 84, 84, 4, 4, 16, 16, -8, 0, 0, 4, 0, 9, 9,
                 -6, -6, 1, 1, -3, -3, -2, -2, 1, 1, 2, 2, -2, 0, -1, -1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1,
                 1, -1, -1, -1, -1],
                [210, 210, -14, 26, 26, 10, 2, 39, 39, -15, -15, -6, -6, 3, 3, 6, 6, -2, 2, 2, -2, 2,
                 5, 5, 0, 0, 7, 7, 1, -1, -1, 1, -2, -2, -5, 1, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
                 0, 3, 3, -3, -3, 0, 0, -1, -1, 1, -1, -1, 0, 0, -84, -84, -4, -4, -16, -16, 8, 0, 0, -4,
                 0, -9, -9, 6, 6, -1, -1, 3, 3, 2, 2, -1, -1, -2, -2, 2, 0, 1, 1, -1, -1, -1, -1, -1, -1, 0,
                 0, 0, 0, 0, 0, -1, -1, 1, 1, 1, 1],
                [420, 420, -28, 20, 20, 36, 4, -30, -30, 24, 24, -12, -12, 6, 6, 12, 12, -4, -4, -4,
                 0, 4, 0, 0, 5, 5, 2, 2, 8, 2, 2, 0, -4, -4, 2, -4, 2, 2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 1, -6, -6, 0, 0, 0, 0, 2, 2, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [300, 300, 12, 20, 20, 20, 12, 30, 30, 30, 30, 3, 3, -6, -6, 8, 8, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 6, 6, 6, 2, 2, 2, 3, 3, 0, 0, 2, 2, 2, 0, -1, -1, 2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2,
                 2, -1, -1, 0, 0, 0, 0, 0, 0, 0, 90, 90, 10, 10, 10, 10, 2, -2, -2, 6, 2, 0, 0, 9, 9, 4, 4, 0,
                 0, 1, 1, -2, -2, 0, 0, 0, 0, 0, 0, 2, 2, -2, -2, 2, 0, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
                [300, 300, 12, 20, 20, 20, 12, 30, 30, 30, 30, 3, 3, -6, -6, 8, 8, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 6, 6, 6, 2, 2, 2, 3, 3, 0, 0, 2, 2, 2, 0, -1, -1, 2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2,
                 2, -1, -1, 0, 0, 0, 0, 0, 0, 0, -90, -90, -10, -10, -10, -10, -2, 2, 2, -6, -2, 0, 0, -9,
                 -9, -4, -4, 0, 0, -1, -1, 2, 2, 0, 0, 0, 0, 0, 0, -2, -2, 2, 2, -2, 0, -1, -1, 1, 1, 0, 0, 0,
                 0, 0, 0, 0, 0],
                [350, 350, -2, -10, -10, -10, -2, 35, 35, 35, 35, -1, -1, -1, -1, 26, 26, 2, -2, -2,
                 -2, 2, 0, 0, 0, 0, -5, -5, -5, -1, -1, -1, 7, 7, 1, 1, -1, -1, -1, 1, 0, 0, 0, 0, 0, -1, -1,
                 -1, -1, 0, 0, 0, -1, -1, -1, -1, -1, -1, 1, 1, 1, 0, 0, 0, 0, 70, 70, -10, -10, 10, 10, 2,
                 2, 2, -2, 2, -5, -5, 7, 7, -1, -1, 1, 1, -1, -1, -1, -1, -4, -4, 0, 0, 0, 0, 5, 5, 1, 1, -1,
                 1, -1, -1, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0],
                [350, 350, -2, -10, -10, -10, -2, 35, 35, 35, 35, -1, -1, -1, -1, 26, 26, 2, -2, -2,
                 -2, 2, 0, 0, 0, 0, -5, -5, -5, -1, -1, -1, 7, 7, 1, 1, -1, -1, -1, 1, 0, 0, 0, 0, 0, -1, -1,
                 -1, -1, 0, 0, 0, -1, -1, -1, -1, -1, -1, 1, 1, 1, 0, 0, 0, 0, -70, -70, 10, 10, -10, -10,
                 -2, -2, -2, 2, -2, 5, 5, -7, -7, 1, 1, -1, -1, 1, 1, 1, 1, 4, 4, 0, 0, 0, 0, -5, -5, -1, -1,
                 1, -1, 1, 1, 0, 0, -1, -1, 0, 0, 1, 1, 0, 0],
                [525, 525, 45, 5, 5, 5, -19, 30, 30, 30, 30, 12, 12, 3, 3, -7, -7, 1, -3, -3, -3, 1, 0,
                 0, 0, 0, 6, 6, 6, 2, 2, 2, 0, 0, 3, 3, -1, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0,
                 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 105, 105, -7, -7, 5, 5, 13, -3, -3, 1, -3, 0, 0, 6, 6,
                 -4, -4, 3, 3, 2, 2, -1, -1, 3, 3, -1, -1, 0, 0, -2, -2, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0],
                [525, 525, 45, 5, 5, 5, -19, 30, 30, 30, 30, 12, 12, 3, 3, -7, -7, 1, -3, -3, -3, 1, 0,
                 0, 0, 0, 6, 6, 6, 2, 2, 2, 0, 0, 3, 3, -1, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0,
                 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, -105, -105, 7, 7, -5, -5, -13, 3, 3, -1, 3, 0, 0, -6,
                 -6, 4, 4, -3, -3, -2, -2, 1, 1, -3, -3, 1, 1, 0, 0, 2, 2, -2, -2, -1, -1, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0],
                [567, 567, -9, 39, 39, -9, -9, 81, 81, 0, 0, 0, 0, 0, 0, 15, 15, -1, -1, -1, 3, -1, 7,
                 7, -3, -3, 9, 9, 0, -3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, -1, -1,
                 1, -3, -3, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 0, 189, 189, -3, -3, 29, 29, -3, -3, -3, -3,
                 -3, 9, 9, 0, 0, -3, -3, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, -1, -1, 3, 3, -1, -1, 0, 0, 0, 0, 0, 0, 0,
                 0, -1, -1, 1, 1, -1, -1],
                [567, 567, -9, 39, 39, -9, -9, 81, 81, 0, 0, 0, 0, 0, 0, 15, 15, -1, -1, -1, 3, -1, 7,
                 7, -3, -3, 9, 9, 0, -3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, -1, -1,
                 1, -3, -3, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 0, -189, -189, 3, 3, -29, -29, 3, 3, 3, 3, 3,
                 -9, -9, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, 1, 1, -3, -3, 1, 1, 0, 0, 0, 0, 0, 0, 0,
                 0, 1, 1, -1, -1, 1, 1],
                [1134, 1134, -18, -18, -18, 30, -18, 0, 0, 81, 81, 0, 0, 0, 0, 30, 30, -2, 6, 6, 2,
                 -2, -6, -6, 4, 4, 0, 0, 9, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, -2, 0, 0, 0, 0, 2, 2,
                 0, 0, 0, -3, -3, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [700, 700, 92, 20, 20, 20, -4, -20, -20, -20, -20, -2, -2, 7, 7, 0, 0, 8, 0, 0, 0, 0,
                 0, 0, 0, 0, -4, -4, -4, -4, -4, -4, 2, 2, -1, -1, -1, -1, -1, -1, 0, 0, 2, -2, -2, 1, 1, 1,
                 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 70, -10, -10, -10, -10, 14, -6, -6,
                 2, -2, 10, 10, -2, -2, 2, 2, -5, -5, 2, 2, -1, -1, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, -1, -1, 0,
                 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
                [700, 700, 92, 20, 20, 20, -4, -20, -20, -20, -20, -2, -2, 7, 7, 0, 0, 8, 0, 0, 0, 0,
                 0, 0, 0, 0, -4, -4, -4, -4, -4, -4, 2, 2, -1, -1, -1, -1, -1, -1, 0, 0, 2, -2, -2, 1, 1, 1,
                 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -70, -70, 10, 10, 10, 10, -14, 6, 6, -2,
                 2, -10, -10, 2, 2, -2, -2, 5, 5, -2, -2, 1, 1, 0, 0, 0, 0, 0, 0, -2, -2, -2, -2, 1, 1, 0, 0,
                 0, 0, -1, -1, 0, 0, 0, 0, 0, 0],
                [700, 700, -4, 60, 60, -20, 12, 55, 55, 10, 10, 7, 7, 4, 4, -4, -4, -4, 4, 4, 0, 0, 0,
                 0, 0, 0, -1, -1, 2, 3, 3, -2, -1, -1, -4, 2, 0, 0, -2, 0, 0, 0, 0, 0, 0, -2, -2, 1, 1, 0, 0,
                 0, -1, -1, 2, 2, -1, -1, 1, 1, 0, 0, 0, 0, 0, 210, 210, 18, 18, 10, 10, -6, 2, 2, -6, 2,
                 15, 15, 3, 3, 3, 3, 0, 0, 3, 3, 0, 0, -2, -2, -2, 0, 0, 0, -3, -3, 1, 1, 0, 0, -1, -1, 0, 0, 0,
                 0, 0, 0, 1, 1, 0, 0],
                [700, 700, -4, 60, 60, -20, 12, 55, 55, 10, 10, 7, 7, 4, 4, -4, -4, -4, 4, 4, 0, 0, 0,
                 0, 0, 0, -1, -1, 2, 3, 3, -2, -1, -1, -4, 2, 0, 0, -2, 0, 0, 0, 0, 0, 0, -2, -2, 1, 1, 0, 0,
                 0, -1, -1, 2, 2, -1, -1, 1, 1, 0, 0, 0, 0, 0, -210, -210, -18, -18, -10, -10, 6, -2, -2,
                 6, -2, -15, -15, -3, -3, -3, -3, 0, 0, -3, -3, 0, 0, 2, 2, 2, 0, 0, 0, 3, 3, -1, -1, 0, 0,
                 1, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0],
                [1400, 1400, -8, -40, -40, 40, 24, 20, 20, 65, 65, 14, 14, 8, 8, -8, -8, -8, 0, 0, 4,
                 0, 0, 0, 0, 0, 4, 4, 1, -4, -4, 1, -2, -2, 4, -2, -4, -4, -2, 0, 0, 0, 0, 0, 0, 2, 2, -1, -1,
                 0, 0, 0, 4, 4, 1, 1, -2, -2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [840, 840, 8, 24, 24, -40, 8, -24, -24, 30, 30, 3, 3, 3, 3, 16, 16, 0, 0, 0, 0, 0, -5,
                 -5, 0, 0, 8, 8, -10, 0, 0, 2, -1, -1, -1, -1, 3, 3, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1,
                 0, 4, 4, -2, -2, 1, 1, 0, 0, 0, 1, 1, 0, 0, 84, 84, 20, 20, -4, -4, -4, 4, 4, -4, -4, -6,
                 -6, 3, 3, 2, 2, 3, 3, -1, -1, -1, -1, 0, 0, 0, 0, -1, -1, 2, 2, 2, 2, -1, -1, 1, 1, 0, 0, 0, 0,
                 1, 1, 0, 0, -1, -1],
                [840, 840, 8, 24, 24, -40, 8, -24, -24, 30, 30, 3, 3, 3, 3, 16, 16, 0, 0, 0, 0, 0, -5,
                 -5, 0, 0, 8, 8, -10, 0, 0, 2, -1, -1, -1, -1, 3, 3, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1,
                 0, 4, 4, -2, -2, 1, 1, 0, 0, 0, 1, 1, 0, 0, -84, -84, -20, -20, 4, 4, 4, -4, -4, 4, 4, 6, 6,
                 -3, -3, -2, -2, -3, -3, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, -2, -2, -2, -2, 1, 1, -1, -1, 0, 0, 0,
                 0, -1, -1, 0, 0, 1, 1],
                [1680, 1680, 16, -80, -80, -16, 16, 60, 60, 6, 6, 6, 6, 6, 6, 32, 32, 0, 0, 0, 0, 0, 0,
                 0, -5, -5, -20, -20, -2, 4, 4, 2, -2, -2, -2, -2, -2, -2, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, -1, -4, -4, 2, 2, 2, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [972, 972, 108, 36, 36, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, -3, -3, -3,
                 -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -2, 2, 2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 162, 162, 18, 18, -6, -6, 18, 6, 6, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, -3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, 0, 0],
                [972, 972, 108, 36, 36, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, -3, -3, -3,
                 -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -2, 2, 2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, -162, -162, -18, -18, 6, 6, -18, -6, -6, -6, -2, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 1, 0, 0, 0, 0],
                [1050, 1050, 58, 50, 50, -30, -6, 15, 15, 15, 15, -3, -3, 6, 6, -10, -10, -2, 2, 2,
                 -2, -2, 0, 0, 0, 0, -17, -17, 7, -1, -1, 3, 1, 1, 4, -2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, 1, 0, 0, 0, 0, 210, 210, 2, 2, -10, -10, 14, -2,
                 -2, -6, -2, 15, 15, 3, 3, -1, -1, 0, 0, -1, -1, 2, 2, -4, -4, 0, 0, 0, 0, -1, -1, -1, -1, 2,
                 0, 1, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0],
                [1050, 1050, 58, 50, 50, -30, -6, 15, 15, 15, 15, -3, -3, 6, 6, -10, -10, -2, 2, 2,
                 -2, -2, 0, 0, 0, 0, -17, -17, 7, -1, -1, 3, 1, 1, 4, -2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, 1, 0, 0, 0, 0, -210, -210, -2, -2, 10, 10, -14,
                 2, 2, 6, 2, -15, -15, -3, -3, 1, 1, 0, 0, 1, 1, -2, -2, 4, 4, 0, 0, 0, 0, 1, 1, 1, 1, -2, 0,
                 -1, -1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
                [2100, 2100, 116, -60, -60, 20, -12, 30, 30, 30, 30, -6, -6, 12, 12, -20, -20, -4,
                 -4, -4, 0, -4, 0, 0, 0, 0, 14, 14, -10, 6, 6, 2, 2, 2, -4, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, -2, -2, -2, -2, -2, -2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0],
                [1344, 1344, 64, 64, 64, 0, 0, 84, 84, -24, -24, -6, -6, -6, -6, 0, 0, 0, 0, 0, 0, 0,
                 -1, -1, 4, 4, 4, 4, -8, 4, 4, 0, -2, -2, 4, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
                 -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 336, 336, 16, 16, 16, 16, 16, 0, 0, 0, 0, 6,
                 6, -6, -6, -2, -2, 0, 0, -2, -2, -2, -2, 0, 0, 0, 0, 1, 1, -2, -2, -2, -2, -2, 0, 0, 0, 0,
                 0, 0, 0, 1, 1, 0, 0, 1, 1],
                [1344, 1344, 64, 64, 64, 0, 0, 84, 84, -24, -24, -6, -6, -6, -6, 0, 0, 0, 0, 0, 0, 0,
                 -1, -1, 4, 4, 4, 4, -8, 4, 4, 0, -2, -2, 4, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
                 -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, -336, -336, -16, -16, -16, -16, -16, 0, 0,
                 0, 0, -6, -6, 6, 6, 2, 2, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, -1, -1, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0,
                 0, -1, -1, 0, 0, -1, -1],
                [2688, 2688, 128, 0, 0, 64, 0, -48, -48, 60, 60, -12, -12, -12, -12, 0, 0, 0, 0, 0,
                 0, 0, 8, 8, 3, 3, -16, -16, -4, 0, 0, 4, -4, -4, -4, 2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [1400, 1400, -72, 40, 40, 40, -8, 50, 50, 50, 50, -4, -4, 5, 5, -16, -16, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, -6, -6, -6, -2, -2, -2, 0, 0, -3, -3, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, -1, -1,
                 -1, 0, 0, 0, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 280, 280, -8, -8, 0, 0, -16, 0, 0, 8, 0,
                 10, 10, 10, 10, -2, -2, 1, 1, -2, -2, 1, 1, 0, 0, 0, 0, 0, 0, -4, -4, 0, 0, -1, -1, 0, 0, 0,
                 0, 1, 1, 0, 0, 0, 0, 0, 0],
                [1400, 1400, -72, 40, 40, 40, -8, 50, 50, 50, 50, -4, -4, 5, 5, -16, -16, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, -6, -6, -6, -2, -2, -2, 0, 0, -3, -3, 1, 1, 1, 1, 0, 0, 0, 0, 0, -1, -1, -1,
                 -1, 0, 0, 0, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, -280, -280, 8, 8, 0, 0, 16, 0, 0, -8, 0,
                 -10, -10, -10, -10, 2, 2, -1, -1, 2, 2, -1, -1, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 1, 1, 0, 0,
                 0, 0, -1, -1, 0, 0, 0, 0, 0, 0],
                [1575, 1575, -57, 15, 15, 15, -9, 90, 90, -45, -45, 9, 9, 0, 0, 11, 11, 3, -1, -1,
                 -1, -1, 0, 0, 0, 0, -6, -6, 3, -6, -6, 3, -3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0,
                 0, 0, 0, 2, 2, -1, -1, -1, -1, 2, 2, -1, 0, 0, 0, 0, 315, 315, -21, -21, 15, 15, -9, 7, 7,
                 3, -1, 0, 0, -9, -9, 0, 0, 0, 0, 3, 3, 0, 0, -3, -3, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0],
                [1575, 1575, -57, 15, 15, 15, -9, 90, 90, -45, -45, 9, 9, 0, 0, 11, 11, 3, -1, -1,
                 -1, -1, 0, 0, 0, 0, -6, -6, 3, -6, -6, 3, -3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0,
                 0, 0, 0, 2, 2, -1, -1, -1, -1, 2, 2, -1, 0, 0, 0, 0, -315, -315, 21, 21, -15, -15, 9, -7,
                 -7, -3, 1, 0, 0, 9, 9, 0, 0, 0, 0, -3, -3, 0, 0, 3, 3, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [3150, 3150, -114, 30, 30, 30, -18, -90, -90, 45, 45, 18, 18, 0, 0, 22, 22, 6, -2,
                 -2, -2, -2, 0, 0, 0, 0, 6, 6, -3, 6, 6, -3, -6, -6, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0,
                 0, 0, 0, -2, -2, 1, 1, -2, -2, -2, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0],
                [2100, 2100, 52, -60, -60, 20, 4, 75, 75, -60, -60, -6, -6, 3, 3, 12, 12, -4, -4,
                 -4, 0, 0, 0, 0, 0, 0, -5, -5, 4, 3, 3, -4, -2, -2, 1, 1, 3, 3, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 3, 3, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 210, 210, -14, -14, 10, 10, 10, -6, -6,
                 2, 2, -15, -15, -6, -6, 1, 1, 3, 3, -2, -2, 1, 1, -2, -2, -2, 0, 0, 0, 1, 1, 1, 1, 1, -1, 0,
                 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
                [2100, 2100, 52, -60, -60, 20, 4, 75, 75, -60, -60, -6, -6, 3, 3, 12, 12, -4, -4,
                 -4, 0, 0, 0, 0, 0, 0, -5, -5, 4, 3, 3, -4, -2, -2, 1, 1, 3, 3, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 3, 3, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, -210, -210, 14, 14, -10, -10, -10, 6, 6,
                 -2, -2, 15, 15, 6, 6, -1, -1, -3, -3, 2, 2, -1, -1, 2, 2, 2, 0, 0, 0, -1, -1, -1, -1, -1, 1,
                 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0],
                [4200, 4200, 104, 40, 40, -40, 8, -120, -120, 15, 15, -12, -12, 6, 6, 24, 24, -8,
                 0, 0, -4, 0, 0, 0, 0, 0, 8, 8, -1, -8, -8, -1, -4, -4, 2, 2, -2, -2, 2, 2, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0],
                [2240, 2240, -64, 64, 64, 0, 0, -4, -4, -40, -40, -10, -10, 2, 2, 0, 0, 0, 0, 0, 0, 0,
                 -5, -5, 0, 0, -4, -4, 8, 4, 4, 0, 2, 2, -4, 2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, -1, -1, -1,
                 -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 336, 336, 16, 16, -16, -16, -16, 0, 0, 0, 0, 6,
                 6, -6, -6, -2, -2, 0, 0, -2, -2, -2, -2, 0, 0, 0, 0, 1, 1, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0,
                 -1, -1, 0, 0, 1, 1],
                [2240, 2240, -64, 64, 64, 0, 0, -4, -4, -40, -40, -10, -10, 2, 2, 0, 0, 0, 0, 0, 0, 0,
                 -5, -5, 0, 0, -4, -4, 8, 4, 4, 0, 2, 2, -4, 2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, -1, -1, -1,
                 -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -336, -336, -16, -16, 16, 16, 16, 0, 0, 0, 0,
                 -6, -6, 6, 6, 2, 2, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, -1, -1, -2, -2, -2, -2, -2, 0, 0, 0, 0, 0, 0,
                 0, 1, 1, 0, 0, -1, -1],
                [4480, 4480, -128, 0, 0, 64, 0, -80, -80, -44, -44, -20, -20, 4, 4, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, -5, -5, 16, 16, 4, 0, 0, 4, 4, 4, 4, -2, 0, 0, -2, 0, 0, 0, 0, 0, 0, -2, -2, 1, 1, 0,
                 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [2268, 2268, -36, 12, 12, -36, 12, 81, 81, 0, 0, 0, 0, 0, 0, -12, -12, 4, -4, -4, 0,
                 0, -2, -2, 3, 3, 9, 9, 0, -3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2,
                 -1, -3, -3, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 0, 378, 378, -6, -6, 10, 10, -6, -6, -6, -6, 2,
                 -9, -9, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, -2, -2, -3, -3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, -1, -1, 1, 1],
                [2268, 2268, -36, 12, 12, -36, 12, 81, 81, 0, 0, 0, 0, 0, 0, -12, -12, 4, -4, -4, 0,
                 0, -2, -2, 3, 3, 9, 9, 0, -3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2,
                 -1, -3, -3, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 0, -378, -378, 6, 6, -10, -10, 6, 6, 6, 6, -2,
                 9, 9, 0, 0, -3, -3, 0, 0, 0, 0, 0, 0, -2, -2, -2, 0, 2, 2, 3, 3, -1, -1, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 1, 1, -1, -1],
                [4536, 4536, -72, -72, -72, -24, 24, 0, 0, 81, 81, 0, 0, 0, 0, -24, -24, 8, 0, 0, -4,
                 0, 6, 6, 1, 1, 0, 0, 9, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 1,
                 0, 0, -3, -3, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [2835, 2835, -45, 51, 51, -45, 3, -81, -81, 0, 0, 0, 0, 0, 0, 3, 3, 3, -5, -5, 3, -1,
                 5, 5, 0, 0, -9, -9, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 1, 1, 0,
                 3, 3, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, 0, 189, 189, -3, -3, -19, -19, -3, -3, -3, -3, 5, 9,
                 9, 0, 0, -3, -3, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, -1, -1, 3, 3, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
                 1, 1, 1, 1, -1, -1],
                [2835, 2835, -45, 51, 51, -45, 3, -81, -81, 0, 0, 0, 0, 0, 0, 3, 3, 3, -5, -5, 3, -1,
                 5, 5, 0, 0, -9, -9, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 1, 1, 0,
                 3, 3, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, 0, -189, -189, 3, 3, 19, 19, 3, 3, 3, 3, -5, -9, -9,
                 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1, 1, 1, -3, -3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1,
                 -1, -1, -1, 1, 1],
                [5670, 5670, -90, -90, -90, 6, 6, 0, 0, -81, -81, 0, 0, 0, 0, 6, 6, 6, 6, 6, -2, -2, 0,
                 0, 5, 5, 0, 0, -9, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, -2, 0, 0, 0, 0, 0, 0, 1, 0, 0,
                 3, 3, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [3200, 3200, 128, 0, 0, 0, 0, -40, -40, -40, -40, 14, 14, -4, -4, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 8, 8, 8, 0, 0, 0, 2, 2, -4, -4, 0, 0, 0, 0, 1, 1, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 160, 160, 32, 32, 0, 0, 0, 0, 0, 0, 0, -20, -20, -2,
                 -2, -4, -4, -2, -2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0,
                 0, 0, 0],
                [3200, 3200, 128, 0, 0, 0, 0, -40, -40, -40, -40, 14, 14, -4, -4, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 8, 8, 8, 0, 0, 0, 2, 2, -4, -4, 0, 0, 0, 0, 1, 1, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -160, -160, -32, -32, 0, 0, 0, 0, 0, 0, 0, 20, 20, 2,
                 2, 4, 4, 2, 2, -2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0,
                 0, 0, 0],
                [4096, 4096, 0, 0, 0, 0, 0, 64, 64, 64, 64, -8, -8, -8, -8, 0, 0, 0, 0, 0, 0, 0, -4, -4,
                 -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, -1, -1, -1, -1, 512, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16, -16, 8, 8, 0, 0,
                 -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0, -1, -1],
                [4096, 4096, 0, 0, 0, 0, 0, 64, 64, 64, 64, -8, -8, -8, -8, 0, 0, 0, 0, 0, 0, 0, -4, -4,
                 -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, -1, -1, -1, -1, -512, -512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, -8, -8, 0, 0,
                 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0, 0, 1, 1],
                [4200, 4200, -24, 40, 40, 40, 8, -30, -30, -30, -30, 15, 15, -3, -3, -8, -8, -8, 0,
                 0, 0, 0, 0, 0, 0, 0, -6, -6, -6, -2, -2, -2, 3, 3, 3, 3, 1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, -2, -2, -2, -2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 420, 420, 4, 4, -20, -20, -4, -4,
                 -4, 4, -4, 0, 0, -3, -3, 4, 4, 3, 3, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, -2, -2, -1, 1, -1, -1,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [4200, 4200, -24, 40, 40, 40, 8, -30, -30, -30, -30, 15, 15, -3, -3, -8, -8, -8, 0,
                 0, 0, 0, 0, 0, 0, 0, -6, -6, -6, -2, -2, -2, 3, 3, 3, 3, 1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, -2, -2, -2, -2, 1, 1, 0, 0, 0, 0, 0, 0, 0, -420, -420, -4, -4, 20, 20, 4, 4, 4,
                 -4, 4, 0, 0, 3, 3, -4, -4, -3, -3, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, -2, -2, 2, 2, 1, -1, 1,
                 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [6075, 6075, 27, -45, -45, -45, -21, 0, 0, 0, 0, 0, 0, 0, 0, -9, -9, -1, 3, 3, 3, 3, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 405, 405, -27, -27, -15, -15, 9, 9, 9, -3, 1, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 3, 3, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
                [6075, 6075, 27, -45, -45, -45, -21, 0, 0, 0, 0, 0, 0, 0, 0, -9, -9, -1, 3, 3, 3, 3, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -405, -405, 27, 27, 15, 15, -9, -9, -9, 3, -1, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, -3, -3, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                [8, -8, 0, 4, -4, 0, 0, 5, -5, -4, 4, -1, 1, 2, -2, 4, -4, 0, 2, -2, 0, 0, 3, -3, -2, 2,
                 -3, 3, 0, 1, -1, 0, 3, -3, 0, 0, -2, 2, 0, 0, 1, -1, 0, 2, -2, 2, -2, -1, 1, -1, 1, 0, 1, -1,
                 -2, 2, 1, -1, -1, 1, 0, 0, 0, 1, -1, 6, -6, 2, -2, 4, -4, 0, 2, -2, 0, 0, 3, -3, -3, 3, -1, 1,
                 0, 0, -1, 1, 2, -2, 2, -2, 0, 0, 1, -1, -3, 3, 1, -1, 0, 0, -1, 1, -1, 1, 0, 0, -1, 1, -1, 1,
                 -2, 2],
                [8, -8, 0, 4, -4, 0, 0, 5, -5, -4, 4, -1, 1, 2, -2, 4, -4, 0, 2, -2, 0, 0, 3, -3, -2, 2,
                 -3, 3, 0, 1, -1, 0, 3, -3, 0, 0, -2, 2, 0, 0, 1, -1, 0, 2, -2, 2, -2, -1, 1, -1, 1, 0, 1, -1,
                 -2, 2, 1, -1, -1, 1, 0, 0, 0, 1, -1, -6, 6, -2, 2, -4, 4, 0, -2, 2, 0, 0, -3, 3, 3, -3, 1, -1,
                 0, 0, 1, -1, -2, 2, -2, 2, 0, 0, -1, 1, 3, -3, -1, 1, 0, 0, 1, -1, 1, -1, 0, 0, 1, -1, 1, -1,
                 2, -2],
                [56, -56, 0, -4, 4, 0, 0, 11, -11, -16, 16, 2, -2, 2, -2, 12, -12, 0, -2, 2, 0, 0, 1,
                 -1, -4, 4, 3, -3, 0, -1, 1, 0, 6, -6, 0, 0, 2, -2, 0, 0, 0, 0, 0, 2, -2, -1, 1, -1, 1, 1, -1,
                 0, 3, -3, 0, 0, 0, 0, 1, -1, 0, 1, -1, -1, 1, 14, -14, -6, 6, 4, -4, 0, 2, -2, 0, 0, -1, 1,
                 -4, 4, 3, -3, 2, -2, 0, 0, 0, 0, -2, 2, 0, 0, -1, 1, -3, 3, 1, -1, 0, 0, 2, -2, 0, 0, -1, 1,
                 -1, 1, 1, -1, -1, 1],
                [56, -56, 0, -4, 4, 0, 0, 11, -11, -16, 16, 2, -2, 2, -2, 12, -12, 0, -2, 2, 0, 0, 1,
                 -1, -4, 4, 3, -3, 0, -1, 1, 0, 6, -6, 0, 0, 2, -2, 0, 0, 0, 0, 0, 2, -2, -1, 1, -1, 1, 1, -1,
                 0, 3, -3, 0, 0, 0, 0, 1, -1, 0, 1, -1, -1, 1, -14, 14, 6, -6, -4, 4, 0, -2, 2, 0, 0, 1, -1,
                 4, -4, -3, 3, -2, 2, 0, 0, 0, 0, 2, -2, 0, 0, 1, -1, 3, -3, -1, 1, 0, 0, -2, 2, 0, 0, 1, -1,
                 1, -1, -1, 1, 1, -1],
                [112, -112, 0, 24, -24, 0, 0, 31, -31, 4, -4, 4, -4, 4, -4, 8, -8, 0, 4, -4, 0, 0, 7,
                 -7, 2, -2, -9, 9, 0, 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, -1, 1, 0,
                 -1, 1, 2, -2, 2, -2, 1, -1, 0, 1, -1, -1, 1, 56, -56, 8, -8, 16, -16, 0, 0, 0, 0, 0, 11,
                 -11, 2, -2, -1, 1, 2, -2, 2, -2, 2, -2, 4, -4, 0, 0, 1, -1, -3, 3, 1, -1, 0, 0, 0, 0, 0, 0,
                 -1, 1, 1, -1, 1, -1, 1, -1],
                [112, -112, 0, 24, -24, 0, 0, 31, -31, 4, -4, 4, -4, 4, -4, 8, -8, 0, 4, -4, 0, 0, 7,
                 -7, 2, -2, -9, 9, 0, 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, -1, 1, 0,
                 -1, 1, 2, -2, 2, -2, 1, -1, 0, 1, -1, -1, 1, -56, 56, -8, 8, -16, 16, 0, 0, 0, 0, 0, -11,
                 11, -2, 2, 1, -1, -2, 2, -2, 2, -2, 2, -4, 4, 0, 0, -1, 1, 3, -3, -1, 1, 0, 0, 0, 0, 0, 0, 1,
                 -1, -1, 1, -1, 1, -1, 1],
                [160, -160, 0, 16, -16, 0, 0, 34, -34, -20, 20, -2, 2, -2, 2, 16, -16, 0, 0, 0, 0, 0,
                 5, -5, 0, 0, -6, 6, 0, -2, 2, 0, 6, -6, 0, 0, -2, 2, 0, 0, -1, 1, 0, 0, 0, 1, -1, 1, -1, 1,
                 -1, 0, -2, 2, -2, 2, -2, 2, 0, 0, 0, -1, 1, 0, 0, 64, -64, 0, 0, 16, -16, 0, 0, 0, 0, 0, 4,
                 -4, -8, 8, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -6, 6, -2, 2, 0, 0, 0, 0, 1, -1, 1, -1,
                 1, -1, 0, 0, -1, 1],
                [160, -160, 0, 16, -16, 0, 0, 34, -34, -20, 20, -2, 2, -2, 2, 16, -16, 0, 0, 0, 0, 0,
                 5, -5, 0, 0, -6, 6, 0, -2, 2, 0, 6, -6, 0, 0, -2, 2, 0, 0, -1, 1, 0, 0, 0, 1, -1, 1, -1, 1,
                 -1, 0, -2, 2, -2, 2, -2, 2, 0, 0, 0, -1, 1, 0, 0, -64, 64, 0, 0, -16, 16, 0, 0, 0, 0, 0, -4,
                 4, 8, -8, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 6, -6, 2, -2, 0, 0, 0, 0, -1, 1, -1, 1,
                 -1, 1, 0, 0, 1, -1],
                [448, -448, 0, -32, 32, 0, 0, 28, -28, -44, 44, -2, 2, 4, -4, 32, -32, 0, 0, 0, 0, 0,
                 -2, 2, -2, 2, 12, -12, 0, 4, -4, 0, 6, -6, 0, 0, 4, -4, 0, 0, 0, 0, 0, 0, 0, -2, 2, 1, -1, -2,
                 2, 0, -4, 4, 2, -2, 2, -2, 0, 0, 0, -2, 2, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [400, -400, 0, 40, -40, 0, 0, 25, -25, -20, 20, 4, -4, 10, -10, -8, 8, 0, 4, -4, 0, 0,
                 0, 0, 0, 0, 9, -9, 0, 1, -1, 0, 0, 0, 0, 0, -2, 2, 0, 0, 1, -1, 0, 0, 0, -2, 2, 1, -1, 0, 0, 0,
                 1, -1, -2, 2, -2, 2, 1, -1, 0, 0, 0, 0, 0, 120, -120, 8, -8, 0, 0, 0, 0, 0, 0, 0, 15, -15,
                 -6, 6, -1, 1, 0, 0, 2, -2, 2, -2, -4, 4, 0, 0, 0, 0, 3, -3, 3, -3, 0, 0, 0, 0, 1, -1, 0, 0, 0,
                 0, -1, 1, 0, 0],
                [400, -400, 0, 40, -40, 0, 0, 25, -25, -20, 20, 4, -4, 10, -10, -8, 8, 0, 4, -4, 0, 0,
                 0, 0, 0, 0, 9, -9, 0, 1, -1, 0, 0, 0, 0, 0, -2, 2, 0, 0, 1, -1, 0, 0, 0, -2, 2, 1, -1, 0, 0, 0,
                 1, -1, -2, 2, -2, 2, 1, -1, 0, 0, 0, 0, 0, -120, 120, -8, 8, 0, 0, 0, 0, 0, 0, 0, -15, 15,
                 6, -6, 1, -1, 0, 0, -2, 2, -2, 2, 4, -4, 0, 0, 0, 0, -3, 3, -3, 3, 0, 0, 0, 0, -1, 1, 0, 0, 0,
                 0, 1, -1, 0, 0],
                [448, -448, 0, 32, -32, 0, 0, 16, -16, 16, -16, 16, -16, -2, 2, 0, 0, 0, 0, 0, 0, 0,
                 -2, 2, -2, 2, 0, 0, 0, 8, -8, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, 2, -2, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, 112, -112, 16, -16, 0, 0, 0, 0, 0, 0, 0, 4, -4, 4,
                 -4, 4, -4, 4, -4, 4, -4, -2, 2, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0,
                 0, -1, 1],
                [448, -448, 0, 32, -32, 0, 0, 16, -16, 16, -16, 16, -16, -2, 2, 0, 0, 0, 0, 0, 0, 0,
                 -2, 2, -2, 2, 0, 0, 0, 8, -8, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, 2, -2, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, -112, 112, -16, 16, 0, 0, 0, 0, 0, 0, 0, -4, 4, -4,
                 4, -4, 4, -4, 4, -4, 4, 2, -2, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0,
                 0, 1, -1],
                [560, -560, 0, 56, -56, 0, 0, 74, -74, 20, -20, -7, 7, 2, -2, 8, -8, 0, 4, -4, 0, 0, 5,
                 -5, 0, 0, -6, 6, 0, 2, -2, 0, -3, 3, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 1, -1, 0,
                 2, -2, 2, -2, -1, 1, -2, 2, 0, -1, 1, 0, 0, 196, -196, 12, -12, 24, -24, 0, 4, -4, 0, 0,
                 16, -16, 7, -7, 0, 0, -2, 2, -3, 3, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1,
                 -1, -1, 1, 0, 0, 1, -1],
                [560, -560, 0, 56, -56, 0, 0, 74, -74, 20, -20, -7, 7, 2, -2, 8, -8, 0, 4, -4, 0, 0, 5,
                 -5, 0, 0, -6, 6, 0, 2, -2, 0, -3, 3, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 1, -1, 0,
                 2, -2, 2, -2, -1, 1, -2, 2, 0, -1, 1, 0, 0, -196, 196, -12, 12, -24, 24, 0, -4, 4, 0, 0,
                 -16, 16, -7, 7, 0, 0, 2, -2, 3, -3, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1,
                 1, 1, -1, 0, 0, -1, 1],
                [1344, -1344, 0, 32, -32, 0, 0, -60, 60, -60, 60, -6, 6, 12, -12, 32, -32, 0, 0, 0,
                 0, 0, -6, 6, -6, 6, -12, 12, 0, -4, 4, 0, -6, 6, 0, 0, -4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 2, -2, 0, -4, 4, 2, -2, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [840, -840, 0, 4, -4, 0, 0, 21, -21, -60, 60, 3, -3, -6, 6, 20, -20, 0, 2, -2, 0, 0,
                 -5, 5, 0, 0, -3, 3, 0, 1, -1, 0, 3, -3, 0, 0, -2, 2, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, -1, 1, 0,
                 5, -5, 2, -2, -1, 1, -1, 1, 0, 1, -1, 0, 0, 126, -126, 10, -10, 4, -4, 0, 2, -2, 0, 0, -9,
                 9, -9, 9, -5, 5, 0, 0, 1, -1, -2, 2, -2, 2, 0, 0, 1, -1, -3, 3, 1, -1, 0, 0, -1, 1, 0, 0, 0,
                 0, -1, 1, 1, -1, 1, -1],
                [840, -840, 0, 4, -4, 0, 0, 21, -21, -60, 60, 3, -3, -6, 6, 20, -20, 0, 2, -2, 0, 0,
                 -5, 5, 0, 0, -3, 3, 0, 1, -1, 0, 3, -3, 0, 0, -2, 2, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, -1, 1, 0,
                 5, -5, 2, -2, -1, 1, -1, 1, 0, 1, -1, 0, 0, -126, 126, -10, 10, -4, 4, 0, -2, 2, 0, 0, 9,
                 -9, 9, -9, 5, -5, 0, 0, -1, 1, 2, -2, 2, -2, 0, 0, -1, 1, 3, -3, -1, 1, 0, 0, 1, -1, 0, 0, 0,
                 0, 1, -1, -1, 1, -1, 1],
                [1008, -1008, 0, 24, -24, 0, 0, 90, -90, 36, -36, 9, -9, 0, 0, 8, -8, 0, -4, 4, 0, 0,
                 3, -3, -2, 2, -6, 6, 0, -6, 6, 0, -3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
                 2, -2, 2, -2, -1, 1, 2, -2, 0, 0, 0, 1, -1, 252, -252, -12, 12, 24, -24, 0, -4, 4, 0, 0,
                 0, 0, 9, -9, 0, 0, 0, 0, 3, -3, 0, 0, 0, 0, 0, 0, -3, 3, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0,
                 -1, 1, 0, 0, 0, 0],
                [1008, -1008, 0, 24, -24, 0, 0, 90, -90, 36, -36, 9, -9, 0, 0, 8, -8, 0, -4, 4, 0, 0,
                 3, -3, -2, 2, -6, 6, 0, -6, 6, 0, -3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
                 2, -2, 2, -2, -1, 1, 2, -2, 0, 0, 0, 1, -1, -252, 252, 12, -12, -24, 24, 0, 4, -4, 0, 0,
                 0, 0, -9, 9, 0, 0, 0, 0, -3, 3, 0, 0, 0, 0, 0, 0, 3, -3, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1,
                 -1, 0, 0, 0, 0],
                [2016, -2016, 0, 48, -48, 0, 0, -90, 90, -36, 36, 18, -18, 0, 0, 16, -16, 0, -8, 8,
                 0, 0, 6, -6, -4, 4, 6, -6, 0, 6, -6, 0, -6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2,
                 2, 0, -2, 2, -2, 2, -2, 2, -2, 2, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [1296, -1296, 0, -24, 24, 0, 0, 81, -81, 0, 0, 0, 0, 0, 0, 24, -24, 0, -4, 4, 0, 0, 1,
                 -1, 6, -6, 9, -9, 0, -3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -3,
                 3, 0, 0, 0, 0, -1, 1, 0, 1, -1, 0, 0, 216, -216, -24, 24, 16, -16, 0, 0, 0, 0, 0, -9, 9, 0,
                 0, 3, -3, 0, 0, 0, 0, 0, 0, -4, 4, 0, 0, 1, -1, -3, 3, 1, -1, 0, 0, 0, 0, -1, 1, 0, 0, 1, -1,
                 -1, 1, 1, -1],
                [1296, -1296, 0, -24, 24, 0, 0, 81, -81, 0, 0, 0, 0, 0, 0, 24, -24, 0, -4, 4, 0, 0, 1,
                 -1, 6, -6, 9, -9, 0, -3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -3,
                 3, 0, 0, 0, 0, -1, 1, 0, 1, -1, 0, 0, -216, 216, 24, -24, -16, 16, 0, 0, 0, 0, 0, 9, -9, 0,
                 0, -3, 3, 0, 0, 0, 0, 0, 0, 4, -4, 0, 0, -1, 1, 3, -3, -1, 1, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1,
                 1, -1, -1, 1],
                [1400, -1400, 0, 60, -60, 0, 0, -25, 25, 20, -20, -13, 13, 8, -8, -4, 4, 0, -2, 2, 0,
                 0, 0, 0, 0, 0, 15, -15, 0, 3, -3, 0, 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, -2, -1, 1, 0,
                 0, 0, -1, 1, 2, -2, -1, 1, 1, -1, 0, 0, 0, 0, 0, 210, -210, 6, -6, -20, 20, 0, -10, 10, 0,
                 0, 15, -15, 3, -3, 3, -3, 0, 0, -3, 3, 0, 0, -2, 2, 0, 0, 0, 0, -3, 3, 1, -1, 0, 0, -1, 1, 0,
                 0, 0, 0, 0, 0, 1, -1, 0, 0],
                [1400, -1400, 0, 60, -60, 0, 0, -25, 25, 20, -20, -13, 13, 8, -8, -4, 4, 0, -2, 2, 0,
                 0, 0, 0, 0, 0, 15, -15, 0, 3, -3, 0, 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, -2, -1, 1, 0,
                 0, 0, -1, 1, 2, -2, -1, 1, 1, -1, 0, 0, 0, 0, 0, -210, 210, -6, 6, 20, -20, 0, 10, -10, 0,
                 0, -15, 15, -3, 3, -3, 3, 0, 0, 3, -3, 0, 0, 2, -2, 0, 0, 0, 0, 3, -3, -1, 1, 0, 0, 1, -1, 0,
                 0, 0, 0, 0, 0, -1, 1, 0, 0],
                [1400, -1400, 0, 60, -60, 0, 0, 95, -95, -40, 40, -4, 4, -4, 4, -4, 4, 0, -2, 2, 0, 0,
                 0, 0, 0, 0, -9, 9, 0, 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 1, -1, 1, 0, 0, 0,
                 -1, 1, -4, 4, 2, -2, 1, -1, 0, 0, 0, 0, 0, 350, -350, 10, -10, 20, -20, 0, -6, 6, 0, 0, 5,
                 -5, -10, 10, 1, -1, 2, -2, -2, 2, -2, 2, 2, -2, 0, 0, 0, 0, 3, -3, -1, 1, 0, 0, 0, 0, 0, 0,
                 -1, 1, 0, 0, -1, 1, 0, 0],
                [1400, -1400, 0, 60, -60, 0, 0, 95, -95, -40, 40, -4, 4, -4, 4, -4, 4, 0, -2, 2, 0, 0,
                 0, 0, 0, 0, -9, 9, 0, 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 1, -1, 1, 0, 0, 0,
                 -1, 1, -4, 4, 2, -2, 1, -1, 0, 0, 0, 0, 0, -350, 350, -10, 10, -20, 20, 0, 6, -6, 0, 0, -5,
                 5, 10, -10, -1, 1, -2, 2, 2, -2, 2, -2, -2, 2, 0, 0, 0, 0, -3, 3, 1, -1, 0, 0, 0, 0, 0, 0, 1,
                 -1, 0, 0, 1, -1, 0, 0],
                [2400, -2400, 0, -80, 80, 0, 0, 60, -60, 60, -60, -3, 3, 6, -6, 16, -16, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 12, -12, 0, 4, -4, 0, -3, 3, 0, 0, -2, 2, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 4, -4, -2, 2, 1, -1, 0, 0, 0, 0, 0, 0, 0, 120, -120, -24, 24, 0, 0, 0, 8, -8, 0, 0, 0,
                 0, 3, -3, 0, 0, 6, -6, -3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, -1, 0, 0, 0,
                 0, 0, 0, 0, 0],
                [2400, -2400, 0, -80, 80, 0, 0, 60, -60, 60, -60, -3, 3, 6, -6, 16, -16, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 12, -12, 0, 4, -4, 0, -3, 3, 0, 0, -2, 2, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 4, -4, -2, 2, 1, -1, 0, 0, 0, 0, 0, 0, 0, -120, 120, 24, -24, 0, 0, 0, -8, 8, 0, 0, 0,
                 0, -3, 3, 0, 0, -6, 6, 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0,
                 0, 0, 0, 0, 0],
                [2800, -2800, 0, -40, 40, 0, 0, 55, -55, -80, 80, -8, 8, 10, -10, -24, 24, 0, -4, 4,
                 0, 0, 0, 0, 0, 0, -9, 9, 0, -1, 1, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, 0,
                 0, 0, 3, -3, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 280, -280, -24, 24, 0, 0, 0, 0, 0, 0, 0, -5,
                 5, -8, 8, 3, -3, -2, 2, 0, 0, 0, 0, 4, -4, 0, 0, 0, 0, 3, -3, 3, -3, 0, 0, 0, 0, 0, 0, 1, -1,
                 0, 0, 1, -1, 0, 0],
                [2800, -2800, 0, -40, 40, 0, 0, 55, -55, -80, 80, -8, 8, 10, -10, -24, 24, 0, -4, 4,
                 0, 0, 0, 0, 0, 0, -9, 9, 0, -1, 1, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, 0,
                 0, 0, 3, -3, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, -280, 280, 24, -24, 0, 0, 0, 0, 0, 0, 0, 5,
                 -5, 8, -8, -3, 3, 2, -2, 0, 0, 0, 0, -4, 4, 0, 0, 0, 0, -3, 3, -3, 3, 0, 0, 0, 0, 0, 0, -1, 1,
                 0, 0, -1, 1, 0, 0],
                [5600, -5600, 0, -80, 80, 0, 0, -10, 10, -100, 100, 2, -2, -4, 4, 16, -16, 0, 8, -8,
                 0, 0, 0, 0, 0, 0, 6, -6, 0, -2, 2, 0, -6, 6, 0, 0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 1, 0,
                 0, 0, -2, 2, -2, 2, -2, 2, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [3240, -3240, 0, 84, -84, 0, 0, 81, -81, 0, 0, 0, 0, 0, 0, -12, 12, 0, 2, -2, 0, 0, -5,
                 5, 0, 0, 9, -9, 0, -3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 2, -2, 0, 0, 0, 0, -1, 1, 0, -3,
                 3, 0, 0, 0, 0, -1, 1, 0, 1, -1, 0, 0, 594, -594, 6, -6, -4, 4, 0, 6, -6, 0, 0, 9, -9, 0, 0,
                 -3, 3, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, -1, 1, 3, -3, -1, 1, 0, 0, 0, 0, -1, 1, 0, 0, 1, -1, 1,
                 -1, -1, 1],
                [3240, -3240, 0, 84, -84, 0, 0, 81, -81, 0, 0, 0, 0, 0, 0, -12, 12, 0, 2, -2, 0, 0, -5,
                 5, 0, 0, 9, -9, 0, -3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 2, -2, 0, 0, 0, 0, -1, 1, 0, -3,
                 3, 0, 0, 0, 0, -1, 1, 0, 1, -1, 0, 0, -594, 594, -6, 6, 4, -4, 0, -6, 6, 0, 0, -9, 9, 0, 0,
                 3, -3, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 1, -1, -3, 3, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1, -1,
                 1, 1, -1],
                [3360, -3360, 0, 16, -16, 0, 0, -6, 6, -60, 60, 12, -12, -6, 6, -16, 16, 0, 0, 0, 0,
                 0, 5, -5, 0, 0, 18, -18, 0, -2, 2, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
                 -1, 0, 2, -2, 2, -2, 2, -2, 0, 0, 0, -1, 1, 0, 0, 336, -336, -16, 16, -16, 16, 0, 0, 0, 0,
                 0, 6, -6, -6, 6, 2, -2, 0, 0, 2, -2, 2, -2, 0, 0, 0, 0, 1, -1, 0, 0, -4, 4, 0, 0, 0, 0, 0, 0,
                 0, 0, -1, 1, 0, 0, 1, -1],
                [3360, -3360, 0, 16, -16, 0, 0, -6, 6, -60, 60, 12, -12, -6, 6, -16, 16, 0, 0, 0, 0,
                 0, 5, -5, 0, 0, 18, -18, 0, -2, 2, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
                 -1, 0, 2, -2, 2, -2, 2, -2, 0, 0, 0, -1, 1, 0, 0, -336, 336, 16, -16, 16, -16, 0, 0, 0, 0,
                 0, -6, 6, 6, -6, -2, 2, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, -1, 1, 0, 0, 4, -4, 0, 0, 0, 0, 0, 0,
                 0, 0, 1, -1, 0, 0, -1, 1],
                [7168, -7168, 0, 0, 0, 0, 0, -128, 128, 16, -16, -32, 32, -8, 8, 0, 0, 0, 0, 0, 0, 0,
                 8, -8, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 1, -1, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [4096, -4096, 0, 0, 0, 0, 0, 64, -64, 64, -64, -8, 8, -8, 8, 0, 0, 0, 0, 0, 0, 0, -4, 4,
                 -4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, -1, 1, -1, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 512, -512, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16, 16, 8, -8, 0, 0,
                 -4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0, -1, 1],
                [4096, -4096, 0, 0, 0, 0, 0, 64, -64, 64, -64, -8, 8, -8, 8, 0, 0, 0, 0, 0, 0, 0, -4, 4,
                 -4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, -1, 1, -1, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, -512, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, -16, -8, 8, 0, 0,
                 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, -1, 0, 0, 0, 0, 1, -1],
                [4200, -4200, 0, 20, -20, 0, 0, -75, 75, 60, -60, 15, -15, 6, -6, 4, -4, 0, 2, -2, 0,
                 0, 0, 0, 0, 0, -3, 3, 0, -7, 7, 0, 3, -3, 0, 0, 2, -2, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0,
                 0, 1, -1, -2, 2, 1, -1, -1, 1, 0, 0, 0, 0, 0, 210, -210, -26, 26, -20, 20, 0, -2, 2, 0, 0,
                 15, -15, 3, -3, -5, 5, 0, 0, 1, -1, -2, 2, 2, -2, 0, 0, 0, 0, -3, 3, 1, -1, 0, 0, 1, -1, 0, 0,
                 0, 0, 0, 0, -1, 1, 0, 0],
                [4200, -4200, 0, 20, -20, 0, 0, -75, 75, 60, -60, 15, -15, 6, -6, 4, -4, 0, 2, -2, 0,
                 0, 0, 0, 0, 0, -3, 3, 0, -7, 7, 0, 3, -3, 0, 0, 2, -2, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0,
                 0, 1, -1, -2, 2, 1, -1, -1, 1, 0, 0, 0, 0, 0, -210, 210, 26, -26, 20, -20, 0, 2, -2, 0, 0,
                 -15, 15, -3, 3, 5, -5, 0, 0, -1, 1, 2, -2, -2, 2, 0, 0, 0, 0, 3, -3, -1, 1, 0, 0, -1, 1, 0, 0,
                 0, 0, 0, 0, 1, -1, 0, 0],
                [4536, -4536, 0, 60, -60, 0, 0, -81, 81, 0, 0, 0, 0, 0, 0, 12, -12, 0, -2, 2, 0, 0, -4,
                 4, 6, -6, -9, 9, 0, 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 3,
                 -3, 0, 0, 0, 0, 1, -1, 0, -1, 1, 0, 0, 378, -378, 30, -30, -20, 20, 0, 6, -6, 0, 0, -9, 9,
                 0, 0, 3, -3, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, -2, 2, -3, 3, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 -1, 1, 1, -1],
                [4536, -4536, 0, 60, -60, 0, 0, -81, 81, 0, 0, 0, 0, 0, 0, 12, -12, 0, -2, 2, 0, 0, -4,
                 4, 6, -6, -9, 9, 0, 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 3,
                 -3, 0, 0, 0, 0, 1, -1, 0, -1, 1, 0, 0, -378, 378, -30, 30, 20, -20, 0, -6, 6, 0, 0, 9, -9,
                 0, 0, -3, 3, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 2, -2, 3, -3, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 1, -1, -1, 1],
                [5600, -5600, 0, -80, 80, 0, 0, 20, -20, 20, -20, 11, -11, 2, -2, -16, 16, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, -12, 12, 0, 4, -4, 0, 3, -3, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1,
                 0, 0, 0, -4, 4, 2, -2, -1, 1, 0, 0, 0, 0, 0, 0, 0, 280, -280, 8, -8, 0, 0, 0, -8, 8, 0, 0,
                 -20, 20, 1, -1, -4, 4, 4, -4, -1, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1,
                 -1, 0, 0, 0, 0, 0, 0],
                [5600, -5600, 0, -80, 80, 0, 0, 20, -20, 20, -20, 11, -11, 2, -2, -16, 16, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, -12, 12, 0, 4, -4, 0, 3, -3, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1,
                 0, 0, 0, -4, 4, 2, -2, -1, 1, 0, 0, 0, 0, 0, 0, 0, -280, 280, -8, 8, 0, 0, 0, 8, -8, 0, 0,
                 20, -20, -1, 1, 4, -4, -4, 4, 1, -1, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0,
                 -1, 1, 0, 0, 0, 0, 0, 0]]
        binv = [0, 120, 8, 68, 2, 74, 32, 8, 56, 4, 64, 24, 12, 36, 4, 52, 20, 8, 44, 14, 38, 12, 36,
              6, 46, 20, 16, 28, 6, 42, 20, 14, 26, 22, 12, 32, 10, 34, 20, 8, 38, 20, 8, 32, 10, 34,
              18, 16, 28, 18, 10, 28, 16, 10, 30, 18, 14, 22, 18, 16, 22, 12, 26, 12, 24, 14, 22, 1,
              91, 19, 49, 3, 63, 7, 55, 25, 7, 43, 9, 39, 5, 47, 19, 13, 31, 9, 39, 19, 13, 33, 11,
              29, 7, 37, 17, 23, 13, 25, 19, 9, 31, 13, 25, 17, 11, 27, 15, 21, 13, 23, 15, 21]
        ainv = [0, 120, 3, 63, 2, 74, 16, 4, 52, 3, 63, 16, 8, 32, 4, 52, 16, 6, 42, 8, 32, 12, 36, 6,
              46, 16, 13, 25, 6, 42, 16, 12, 24, 16, 10, 30, 8, 32, 20, 7, 37, 16, 8, 32, 8, 32,
              16, 13, 25, 16, 10, 28, 16, 10, 30, 16, 14, 22, 16, 15, 21, 11, 26, 12, 24, 14, 22,
              1, 91, 7, 37, 3, 63, 4, 52, 16, 6, 42, 7, 37, 5, 47, 16, 10, 28, 7, 37, 16, 10, 30,
              10, 28, 7, 37, 15, 21, 13, 25, 16, 9, 31, 12, 24, 16, 11, 26, 15, 21, 13, 23, 15, 21]
        nam = ["1_x", "1_x'", "28_x", "28_x'", "35_x", "35_x'", "70_y", "50_x", "50_x'",
             "84_x", "84_x'", "168_y", "175_x", "175_x'", "210_x", "210_x'", "420_y",
             "300_x", "300_x'", "350_x", "350_x'", "525_x", "525_x'", "567_x",
             "567_x'", "1134_y", "700_xx", "700_xx'", "700_x", "700_x'", "1400_y",
             "840_x", "840_x'", "1680_y", "972_x", "972_x'", "1050_x", "1050_x'",
             "2100_y", "1344_x", "1344_x'", "2688_y", "1400_x", "1400_x'", "1575_x",
             "1575_x'", "3150_y", "2100_x", "2100_x'", "4200_y", "2240_x", "2240_x'",
             "4480_y", "2268_x", "2268_x'", "4536_y", "2835_x", "2835_x'", "5670_y",
             "3200_x", "3200_x'", "4096_x", "4096_x'", "4200_x", "4200_x'", "6075_x",
             "6075_x'", "8_z", "8_z'", "56_z", "56_z'", "112_z", "112_z'", "160_z",
             "160_z'", "448_w", "400_z", "400_z'", "448_z", "448_z'", "560_z",
             "560_z'", "1344_w", "840_z", "840_z'", "1008_z", "1008_z'", "2016_w",
             "1296_z", "1296_z'", "1400_zz", "1400_zz'", "1400_z", "1400_z'",
             "2400_z", "2400_z'", "2800_z", "2800_z'", "5600_w", "3240_z",
             "3240_z'", "3360_z", "3360_z'", "7168_w", "4096_z", "4096_z'",
             "4200_z", "4200_z'", "4536_z", "4536_z'", "5600_z", "5600_z'"]
    if typ[0] == 'H' and n == 3:
        ir5 = ir(5)
        if chars:
            ti = [[1, -1, 1, 1, 1, -1, 1, -1, -1, -1],
                [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                [5, -1, 0, 1, -1, 0, 0, 1, 0, -5],
                [5, 1, 0, 1, -1, 0, 0, -1, 0, 5],
                [3, -1, ir5, -1, 0, 1 - ir5, 1 - ir5, 0, ir5, 3],
                [3, -1, 1 - ir5, -1, 0, ir5, ir5, 0, 1 - ir5, 3],
                [3, 1, ir5, -1, 0, ir5 - 1, 1 - ir5, 0, -ir5, -3],
                [3, 1, 1 - ir5, -1, 0, -ir5, ir5, 0, ir5 - 1, -3],
                [4, 0, -1, 0, 1, 1, -1, -1, 1, -4],
                [4, 0, -1, 0, 1, -1, -1, 1, -1, 4]]
        binv = [15, 0, 5, 2, 6, 8, 1, 3, 3, 4]
        ainv = [15, 0, 5, 2, 6, 6, 1, 1, 3, 3]
        nam = ["1_r'", "1_r", "5_r'", "5_r", "3_s", "overline{3}_s", "3_s'",
              "overline{3}_s'", "4_r'", "4_r"]
    if typ[0] == 'H' and n == 4:
        ir5 = ir(5)
        if chars:
            ti = [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                 1, 1],
                [1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1,
                 1, 1, 1, 1, 1, 1, 1],
                [4, 2, 1 + ir5, 0, 1, ir5, ir5 - 1, -1, 0, 2 - ir5, ir5 - 1, 1, -ir5, 0, ir5, 1 - ir5,
                 0, +2 * ir5, 1, -2, -2 + ir5, 1 - ir5, 0, 2, -1, -2 + 2 * ir5, -1, -ir5, 0, 2 - 2 * ir5,
                 -1 - ir5, -2, -2 * ir5, -4],
                [4, -2, 1 + ir5, 0, 1, -ir5, 1 - ir5, 1, 0, 2 - ir5, ir5 - 1, -1, ir5, 0, ir5,
                 ir5 - 1, 0, +2 * ir5, 1, 2, -2 + ir5, 1 - ir5, 0, 2, -1, -2 + 2 * ir5, -1, -ir5, 0, 2 - 2 * ir5,
                 -1 - ir5, -2, -2 * ir5, -4],
                [4, 2, 2 - ir5, 0, 1, 1 - ir5, -ir5, -1, 0, 1 + ir5, -ir5, 1, ir5 - 1, 0, 1 - ir5,
                 ir5, 0, 2 - 2 * ir5, 1, -2, -1 - ir5, ir5, 0, 2, -1, -2 * ir5, -1, ir5 - 1, 0, +2 * ir5,
                 -2 + ir5, -2, -2 + 2 * ir5, -4],
                [4, -2, 2 - ir5, 0, 1, ir5 - 1, ir5, 1, 0, 1 + ir5, -ir5, -1, 1 - ir5, 0, 1 - ir5,
                 -ir5, 0, 2 - 2 * ir5, 1, 2, -1 - ir5, ir5, 0, 2, -1, -2 * ir5, -1, ir5 - 1, 0, +2 * ir5,
                 -2 + ir5, -2, -2 + 2 * ir5, -4],
                [6, 0, +2 * ir5, -2, 0, 0, 0, 0, 0, 2 - 2 * ir5, 1 - ir5, 0, 0, -ir5, ir5, 0, -1,
                 3 + ir5, 1, 0, 2 - 2 * ir5, 1 - ir5, ir5 - 1, 3, 0, 4 - ir5, 1, ir5, 2, 4 - ir5, +2 * ir5, 3,
                 3 + ir5, 6],
                [6, 0, 2 - 2 * ir5, -2, 0, 0, 0, 0, 0, +2 * ir5, ir5, 0, 0, ir5 - 1, 1 - ir5, 0, -1,
                 4 - ir5, 1, 0, +2 * ir5, ir5, -ir5, 3, 0, 3 + ir5, 1, 1 - ir5, 2, 3 + ir5, 2 - 2 * ir5, 3,
                 4 - ir5, 6],
                [8, 0, -2, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 1, 3, -2, 0, -2, 0, -1, 5, 2, 3, -2, 0,
                 4, 3, -2, 5, 3, 8],
                [8, 0, -2, 0, 2, 0, 0, 0, 0, -2, -1, 0, 0, 0, 1, 0, 0, 2, -3, 0, 2, 1, 0, 4, -2, -2, 3, -1,
                 0, 2, 2, -4, -2, -8],
                [9, 3, 1 + ir5, 1, 0, ir5, 1 - ir5, 0, -1, 2 - ir5, 0, 0, ir5, ir5 - 1, 0, 1 - ir5, 0,
                 +3 * ir5, -1, 3, 2 - ir5, 0, -ir5, 0, 0, 3 - 3 * ir5, -1, 0, -3, 3 - 3 * ir5, 1 + ir5, 0,
                 +3 * ir5, 9],
                [9, -3, 1 + ir5, 1, 0, -ir5, ir5 - 1, 0, 1, 2 - ir5, 0, 0, -ir5, ir5 - 1, 0, ir5 - 1,
                 0, +3 * ir5, -1, -3, 2 - ir5, 0, -ir5, 0, 0, 3 - 3 * ir5, -1, 0, -3, 3 - 3 * ir5,
                 1 + ir5, 0, +3 * ir5, 9],
                [9, 3, 2 - ir5, 1, 0, 1 - ir5, ir5, 0, -1, 1 + ir5, 0, 0, 1 - ir5, -ir5, 0, ir5, 0,
                 3 - 3 * ir5, -1, 3, 1 + ir5, 0, ir5 - 1, 0, 0, +3 * ir5, -1, 0, -3, +3 * ir5, 2 - ir5, 0,
                 3 - 3 * ir5, 9],
                [9, -3, 2 - ir5, 1, 0, ir5 - 1, -ir5, 0, 1, 1 + ir5, 0, 0, ir5 - 1, -ir5, 0, -ir5, 0,
                 3 - 3 * ir5, -1, -3, 1 + ir5, 0, ir5 - 1, 0, 0, +3 * ir5, -1, 0, -3, +3 * ir5, 2 - ir5, 0,
                 3 - 3 * ir5, 9],
                [10, 0, 0, 2, -2, 0, 0, 0, 0, 0, -1, 0, 0, 1, -1, 0, 0, 5, 0, 0, 0, -1, 1, 4, -2, 5, 0, -1,
                 6, 5, 0, 4, 5, 10],
                [16, 0, +2 * ir5, 0, -2, 0, 0, 0, 0, 2 - 2 * ir5, -ir5, 0, 0, 0, 1 - ir5, 0, 0, 2 + 4 * ir5,
                 -1, 0, -2 + 2 * ir5, ir5, 0, 2, 2, -6 + 4 * ir5, 1, ir5 - 1, 0, 6 - 4 * ir5, -2 * ir5, -2,
                 -2 - 4 * ir5, -16],
                [16, 0, 2 - 2 * ir5, 0, -2, 0, 0, 0, 0, +2 * ir5, ir5 - 1, 0, 0, 0, ir5, 0, 0, 6 - 4 * ir5,
                 -1, 0, -2 * ir5, 1 - ir5, 0, 2, 2, -2 - 4 * ir5, 1, -ir5, 0, 2 + 4 * ir5, -2 + 2 * ir5, -2,
                 -6 + 4 * ir5, -16],
                [16, 4, 1, 0, 1, 1, -1, 1, 0, 1, 1, -1, -1, 0, -1, 1, 0, 4, -1, -4, -1, -1, 0, -4, -1, -4,
                 1, 1, 0, 4, -1, 4, -4, -16],
                [16, -4, 1, 0, 1, -1, 1, -1, 0, 1, 1, 1, 1, 0, -1, -1, 0, 4, -1, 4, -1, -1, 0, -4, -1, -4,
                 1, 1, 0, 4, -1, 4, -4, -16],
                [16, 4, 1, 0, 1, -1, -1, 1, 0, 1, -1, 1, -1, 0, -1, -1, 0, -4, 1, 4, 1, -1, 0, 4, 1, -4, 1,
                 -1, 0, -4, 1, 4, -4, 16],
                [16, -4, 1, 0, 1, 1, 1, -1, 0, 1, -1, -1, 1, 0, -1, 1, 0, -4, 1, -4, 1, -1, 0, 4, 1, -4, 1,
                 -1, 0, -4, 1, 4, -4, 16],
                [18, 0, -2, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 3, 3, 0, -2, 0, -1, 0, 0, 3, 3, 0,
                 -6, 3, -2, 0, 3, 18],
                [24, 0, -2 * ir5, 0, 0, 0, 0, 0, 0, -2 + 2 * ir5, 1, 0, 0, 0, -1, 0, 0, -2 + 6 * ir5, 1, 0,
                 2 - 2 * ir5, -1, 0, 6, 0, -4 + 6 * ir5, -1, 1, 0, 4 - 6 * ir5, +2 * ir5, -6, 2 - 6 * ir5, -24],
                [24, 0, -2 + 2 * ir5, 0, 0, 0, 0, 0, 0, -2 * ir5, 1, 0, 0, 0, -1, 0, 0, 4 - 6 * ir5, 1, 0,
                 +2 * ir5, -1, 0, 6, 0, 2 - 6 * ir5, -1, 1, 0, -2 + 6 * ir5, 2 - 2 * ir5, -6, -4 + 6 * ir5, -24],
                [24, 0, -2 * ir5, 0, 0, 0, 0, 0, 0, -2 + 2 * ir5, 1 - ir5, 0, 0, 1, ir5, 0, -1, -3 + 4 * ir5,
                 -1, 0, -2 + 2 * ir5, 1 - ir5, 1, 3, 0, 1 - 4 * ir5, -1, ir5, -4, 1 - 4 * ir5, -2 * ir5, 3,
                 -3 + 4 * ir5, 24],
                [24, 0, -2 + 2 * ir5, 0, 0, 0, 0, 0, 0, -2 * ir5, ir5, 0, 0, 1, 1 - ir5, 0, -1, 1 - 4 * ir5,
                 -1, 0, -2 * ir5, ir5, 1, 3, 0, -3 + 4 * ir5, -1, 1 - ir5, -4, -3 + 4 * ir5, -2 + 2 * ir5, 3,
                 1 - 4 * ir5, 24],
                [25, 5, 0, 1, 1, 0, 0, -1, 1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 5, 0, 0, 0, -5, 1, 0, 0, 0, 5,
                 0, 0, -5, 0, 25],
                [25, -5, 0, 1, 1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, -5, 0, 0, 0, -5, 1, 0, 0, 0, 5,
                 0, 0, -5, 0, 25],
                [30, 0, 0, -2, 0, 0, 0, 0, 0, 0, ir5 - 1, 0, 0, 1 - ir5, -ir5, 0, 1, +5 * ir5, 0, 0, 0,
                 ir5 - 1, ir5, -3, 0, 5 - 5 * ir5, 0, -ir5, -2, 5 - 5 * ir5, 0, -3, +5 * ir5, 30],
                [30, 0, 0, -2, 0, 0, 0, 0, 0, 0, -ir5, 0, 0, ir5, ir5 - 1, 0, 1, 5 - 5 * ir5, 0, 0, 0, -ir5,
                 1 - ir5, -3, 0, +5 * ir5, 0, ir5 - 1, -2, +5 * ir5, 0, -3, 5 - 5 * ir5, 30],
                [36, 6, 1, 0, 0, -1, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, -6, -1, -6, -1, 0, 0, 0, 0, 6, 1, 0,
                 0, -6, -1, 0, 6, -36],
                [36, -6, 1, 0, 0, 1, -1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, -6, -1, 6, -1, 0, 0, 0, 0, 6, 1, 0,
                 0, -6, -1, 0, 6, -36],
                [40, 0, 0, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0, -1, 1, 0, 1, -5, 0, 0, 0, 1, -1, 1, -2, -5, 0, 1,
                 4, -5, 0, 1, -5, 40],
                [48, 0, -2, 0, 0, 0, 0, 0, 0, -2, -1, 0, 0, 0, 1, 0, 0, 2, 2, 0, 2, 1, 0, -6, 0, -2, -2, -1,
                 0, 2, 2, 6, -2, -48]]
        binv = [0, 60, 1, 31, 7, 37, 12, 20, 12, 13, 2, 22, 6, 26, 12, 11, 13, 3, 21, 6, 18, 10,
                11, 7, 12, 6, 4, 16, 10, 10, 5, 15, 8, 9]
        ainv = [0, 60, 1, 31, 1, 31, 6, 6, 6, 6, 2, 22, 2, 22, 6, 6, 6, 3, 18, 3, 18, 6, 6, 6, 6, 6, 4,
              16, 6, 6, 5, 15, 6, 6]
        nam = ["1_r", "1_r'", "4_t", "4_t'", "overline{4}_t", "overline{4}_t'", "6_s",
             "overline{6}_s", "8_r", "8_{rr}", "9_s", "9_s'", "overline{9}_s",
             "overline{9}_s'", "10_r", "16_t", "overline{16}_t", "16_{rr}",
             "16_{rr}'", "16_r", "16_r'", "18_r", "24_t", "overline{24}_t", "24_s",
             "overline{24}_s", "25_r", "25_r'", "30_s", "overline{30}_s",
             "36_{rr}", "36_{rr}'", "40_r", "48_{rr}"]
    if typ[0] == 'I':
        m = int(typ[1:])
        if m == 5:
            if chars:
                ti = [[1, 1, 1, 1], [1, -1, 1, 1],
                    [2, 0, ir(5) - 1, -ir(5)], [2, 0, -ir(5), ir(5) - 1]]
            binv = [0, 5, 1, 2]
            ainv = [0, 5, 1, 1]
            nam = ["phi_{1, 0}", "phi_{1, 5}", "phi_{2, 1}", "phi_{2, 2}"]
        else:
            c = conjclassdata(typ, n)['reps']
            z = rootof1(m)
            if m % 2 == 0:
                binv = [0, m // 2, m // 2, m]
                ainv = [0, 1, 1, m]
                nam = ["phi_{1, 0}", "phi_{1, " + str(m // 2) + "}'", "phi_{1, " + str(m // 2) + "}''",
                     "phi_{1, " + str(m) + "}"]
                ti = [len(c) * [1], [(-1)**i.count(1) for i in c], [(-1)**i.count(0)
                                           for i in c], [(-1)**len(i) for i in c]]
                for j in range(1, (m - 2) // 2 + 1):
                    binv.append(j)
                    ainv.append(1)
                    nam.append("phi_{2, " + str(j) + "}")
                    chi = [2, 0, 0]
                    chi.extend([z**(j * len(i) // 2) + z**(-j * len(i) // 2)
                               for i in c[3:]])
                    ti.append(chi)
            else:
                binv = [0, m]
                ainv = [0, m]
                nam = ["phi_{1, 0}", "phi_{1, " + str(m) + "}"]
                ti = [len(c) * [1], [(-1)**len(i) for i in c]]
                for j in range(1, (m - 1) // 2 + 1):
                    binv.append(j)
                    ainv.append(1)
                    nam.append("phi_{2, " + str(j) + "}")
                    chi = [2, 0]
                    chi.extend([z**(j * len(i) // 2) + z**(-j * len(i) // 2)
                               for i in c[2:]])
                    ti.append(chi)
    return {'irreducibles': ti, 'names': nam, 'b': binv, 'a1': ainv}

# F chartable


def chartable(W, chars=True):
    """returns the  ordinary  character table  of W,  together with related
    additional information.

    The result is a dictionary with at least the following entries:

    - classlengths  --  sizes of the conjugacy classes
    - classnames    --  see help to 'conjugacyclasses'
    - classreps     --  representatives of minimal length
    - charnames     --  tuples of names for the characters put together
      from the irreducible components of W
    - irreducibles  --  square matrix of character values
    - position_id   --  position of trivial character
    - position_sgn  --  position of sign character
    - position_refl --  position of reflection character (W irreducible)
    - permsgn       --  permutation induced by tensoring with sign
    - b             --  b-invariants (see also 'fakedegree')
    - a             --  a-invariants (with respect to equal parameters;
      see also 'ainvariants').

    The most expensive part of this function  is the  computation of the
    character table.  If the optional argument  'chars' is set to False,
    then the entry  'irreducibles'  will be omitted,  in which case  the
    result  of the  function  is roughly  equivalent  to the  gap-chevie
    function 'ChevieCharInfo'.

    The  raw data  for the  various types of  irreducible finite Coxeter
    groups  are   explicitly  stored  in  this   module  and  called via
    'irrchardata(typ, n)'.  For  a  general  W  the  data  are then built
    together  from the irreducible components using  'W.cartantype'. See
    also 'chartablesymmetric', 'chartableB', 'chartableD'.

    >>> chartable(coxeter("G", 2))
    {'a': [0, 6, 1, 1, 1, 1],
     'b': [0, 6, 3, 3, 1, 2],
     'charnames': [('phi_{1, 0}',),
      ('phi_{1, 6}',),
      ("phi_{1, 3}'",),
      ("phi_{1, 3}''",),
      ('phi_{2, 1}',),
      ('phi_{2, 2}',)],
     'classlengths': [1, 3, 3, 2, 2, 1],
     'classnames': [(' ',),
      ('~A_1',),
      ('A_1',),
      ('G_2',),
      ('A_2',),
      ('A_1+~A_1',)],
     'classreps': [[], [1], [0], [0, 1], [0, 1, 0, 1], [0, 1, 0, 1, 0, 1]],
     'irreducibles': [[1, 1, 1, 1, 1, 1],
      [1, -1, -1, 1, 1, 1],
      [1, 1, -1, -1, 1, -1],
      [1, -1, 1, -1, 1, -1],
      [2, 0, 0, 1, -1, -2],
      [2, 0, 0, -1, -1, 2]],
     'permsgn': [1, 0, 3, 2, 4, 5],
     'position_id': 0,
     'position_refl': 4,
     'position_sgn': 1}

    See also 'displaychartable'.
    """
    if 'chartable' in dir(W) and (chars is False or
                                  'irreducibles' in W.chartable):
        return W.chartable
    t0 = irrchardata(W.cartantype[0][0], len(W.cartantype[0][1]), chars)
    mat = t0['irreducibles']
    bs = [t0['b']]
    a1s = [t0['a1']]
    nam = [t0['names']]
    for t in W.cartantype[1:]:
        ti = irrchardata(t[0], len(t[1]))
        mat = kroneckerproduct(mat, ti['irreducibles'])
        bs.append(ti['b'])
        a1s.append(ti['a1'])
        nam.append(ti['names'])
    nb = [sum(bi) for bi in cartesian(bs)]
    na1 = [sum(ai) for ai in cartesian(a1s)]
    nnam = [tuple(st) for st in cartesian(nam)]
    cw = conjugacyclasses(W)
    if 'chartable' not in dir(W):
        W.chartable = {'charnames': nnam, 'classnames': cw['classnames'],
                       'classlengths': cw['classlengths'],
                       'classreps': cw['reps'], 'b': nb, 'a': na1}
    if chars:
        sgn = [(-1)**len(w) for w in cw['reps']]
        sp = [mat.index([l[j] * sgn[j] for j in range(len(cw['reps']))])
              for l in mat]
        if len(W.cartantype) > 1:
            prf = False
        else:
            prefl = [(mat[i][0], nb[i]) for i in range(len(nb))]
            if len(W.rank) == 0:
                prf = 1
            else:
                prf = prefl.index((len(W.rank), 1))
        W.chartable['irreducibles'] = mat
        W.chartable['position_id'] = mat.index(len(cw['reps']) * [1])
        W.chartable['position_sgn'] = mat.index(sgn)
        W.chartable['position_refl'] = prf
        W.chartable['permsgn'] = sp
    return W.chartable

# F displaychartable


def displaychartable(ti):
    """displays the character table of a Coxeter group (or of an
    Iwahori-Hecke algebra) in a user-friendly way,  where the
    labelling of the classes and characters is included.

    >>> displaychartable(heckechartable(coxeter("G", 2), [v, v**2]))
    ──────────────────────────────────────────────────────────────────────────────
                      ~A_1     A_1   G_2   A_2 A_1+~A_1
    ──────────────────────────────────────────────────────────────────────────────
      phi_{1, 0} 1    v**4    v**2  v**6 v**12    v**18
      phi_{1, 6} 1      -1      -1     1     1        1
     phi_{1, 3}' 1    v**4      -1 -v**4  v**8   -v**12
    phi_{1, 3}'' 1      -1    v**2 -v**2  v**4    -v**6
      phi_{2, 1} 2 -1+v**4 -1+v**2  v**3 -v**6  -2*v**9
      phi_{2, 2} 2 -1+v**4 -1+v**2 -v**3 -v**6   2*v**9

    See also 'displaymat'.
    """
    if 'charnames' not in ti:
        rows = ['|'.join(c) for c in ti['coxeter'].chartable['charnames']]
        cols = ['|'.join(c) for c in ti['coxeter'].chartable['classnames']]
    else:
        rows = ['|'.join(c) for c in ti['charnames']]
        cols = ['|'.join(c) for c in ti['classnames']]
    displaymat(ti['irreducibles'], rows, cols)


def inductiontable(H, W, display=False, invchar=False):
    """computes  the decomposition  of the  induced characters from the
    subgroup H into irreducible characters of W. The rows correspond
    to the characters of  W,  the  columns to those of the subgroup.
    The result is a dictionary with entries:

        scalar      : the induction table proper
        charW       : names of the characters of W
        charH       : names of the characters of H

    >>> W = coxeter("B", 3)
    >>> H = reflectionsubgroup(W, [1, 2, 5]); H.cartantype  # non-parabolic
    [['A', [0, 1, 2]]]
    >>> inductiontable(H, W)
    {'charH': [('[1, 1, 1, 1]',),
      ('[2, 1, 1]',),
      ('[2, 2]',),
      ('[3, 1]',),
      ('[4]',)],
     'charW': [('[[1, 1, 1], []]',),
      ('[[1, 1], [1]]',),
      ('[[1], [1, 1]]',),
      ('[[], [1, 1, 1]]',),
      ('[[2, 1], []]',),
      ('[[1], [2]]',),
      ('[[2], [1]]',),
      ('[[], [2, 1]]',),
      ('[[3], []]',),
      ('[[], [3]]',)],
     'scalar': [[1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0],
      [0, 1, 0, 0, 0],
      [1, 0, 0, 0, 0],
      [0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0],
      [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0],
      [0, 0, 0, 0, 1],
      [0, 0, 0, 0, 1]]}

    With the optional argument 'invchar' one can specify a numerical
    function  on the  irreducible characters  by which the induction
    will be truncated, for example:

    >>> inductiontable(H, W,                       # not tested
    ...           invchar=(lambda G:chartable(G, chars=False)['b']))

    will yield the Lusztig-Macdonald-Spaltenstein induction.

    See also 'chartable'.
    """
    ch = chartable(H)
    tab = {'charH': ch['charnames'][:], 'charW': chartable(W)['charnames'][:]}
    f = fusionconjugacyclasses(H, W)
    m = len(ch['classlengths'])
    mat = []
    for t in chartable(W)['irreducibles']:
        res = [t[f[k]] for k in range(m)]
        norm = sum(res[k] * res[k] * ch['classlengths'][k]
                 for k in range(m)) // H.order
        vec = m * [0]
        norm1 = 0
        j = 0
        while j < m and norm1 < norm:
            vec[j] = sum(res[k] * ch['irreducibles'][j][k] *
                      ch['classlengths'][k] for k in range(m)) // H.order
            # vec[j]=int(0.5+sum(res[k]*ch['irreducibles'][j][k]*
            #          ch['classlengths'][k] for k in range(m))//H.order)
            norm1 += vec[j]**2
            j += 1
        mat.append(vec)
        # tab['scalar'].append(vec[:])
    if invchar is not False:
        aW = invchar(W)
        aH = invchar(H)
        for i in range(len(mat)):
            for j in range(len(mat[0])):
                if aW[i] != aH[j]:
                    mat[i][j] = 0
    tab['scalar'] = mat
    if display:
        displaymat(mat, tab['charW'], tab['charH'])
    return tab


def checkrepr(W, perms):
    """
    Check the Coxeter relations.
    """
    eins = tuple(range(len(perms[0])))
    for s in W.rank:
        if permmult(perms[s], perms[s]) != eins:
            return False
        for t in range(s):
            p1 = permmult(perms[s], perms[t])
            p = p1[:]
            for i in range(W.coxetermat[s][t] - 1):
                p = permmult(p, p1)
            if p != eins:
                return False
    return True


def involutionmodel(W, poids=1, verbose=False):
    """returns the characters afforded by Kottwitz's involution module.
    This is equivalent  to the characters later described by Lusztig
    and Vogan.  Let  M be a  vector space with a basis {a_w} where w
    runs over the set of involutions in W. According to

      R. Kottwitz, Involutions in Weyl groups, Represent. Theory 4
                                                      (2000), 1--15,

      G. Lusztig and D. A. Vogan, Jr., Hecke algebras and
                 involutions in Weyl groups, Bull. Inst. Math. Acad.
                                    Sinica (N.S.) 7 (2012), 323--354

    the group W acts on M via:

        s.a_w = -a_w      if sw=ws and l(ws)<l(w),

        s.a_w =  a_{sws}  otherwise.

    M  decomposes  as a direct sum of  modules corresponding  to the
    conjugacy classes of involutions.

    The result is a dictionary with keys given by representatives of
    the  conjugacy classes of  involutions  and values  given by the
    decompositions into irreducibles  of the corresponding pieces of
    the  involution module.  (The representatives of involutions are
    taken from the 'reps' component of 'conjugacyclasses(W)').

    >>> involutionmodel(coxeter("H", 3))
    {'[0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2]': [1,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0],
     '[0, 2]': [0, 0, 0, 1, 1, 1, 0, 0, 0, 1],
     '[0]': [0, 0, 1, 0, 0, 0, 1, 1, 1, 0],
     '[]': [0, 1, 0, 0, 0, 0, 0, 0, 0, 0]}

    See also 'involutions' and 'conjugacyclasses'.
    """
    if isinstance(poids, int):
        lp = len(W.rank) * [poids]
    else:
        lp = poids
    rr = conjugacyclasses(W)['reps']
    ti = chartable(W)
    cl = [w for w in rr if W.wordtocoxelm(2 * w) == tuple(W.rank)]
    # cl=[w for w in rr if conjugacyclasses(W)['classlengths'][rr.index(w)]==
    #                                                      len(classmin(W, w))]
    # cl=rr
    # lprint('# Number of involutions = '+str(sum([len(l) for l in cl]))+'\n')
    chisigma = {}
    for x in cl:
        inv = conjugacyclass(W, W.wordtoperm(x))
        cinv = [bytes(y[:len(W.rank)]) for y in inv]
        perms = []
        if verbose:
            lprint('#I ')
        for s in W.rank:
            if verbose:
                lprint(str(s) + ' ')
            p = (2 * len(inv)) * [0]
            for i in range(len(inv)):
                i1 = cinv.index(bytes(conjgenperm(W, s, inv[i])[:len(W.rank)]))
                if i == i1 and inv[i][s] >= W.N and lp[s] % 2 == 1:
                    p[i] = len(inv) + i1
                    p[len(inv) + i] = i1
                else:
                    p[i] = i1
                    p[len(inv) + i] = len(inv) + i1
            perms.append(p)
        char = []
        for w in rr:
            if w == []:
                char.append(len(inv))
            else:
                l = [list(range(len(inv)))]
                l.extend([perms[s] for s in w])
                p = reduce(permmult, tuple(l))
                c = 0
                for i in range(len(inv)):
                    if p[i] == i:
                        c += 1
                    if p[i] == len(inv) + i:
                        c -= 1
                char.append(c)
        chisigma[str(x)] = [sum([char[j] * chi[j] * ti['classlengths'][j]
              for j in range(len(rr))]) // W.order for chi in ti['irreducibles']]
        if verbose:
            lprint('\n')
    if verbose:
        lprint('#I Total decomposition:\n#I ')
        lprint(str([sum([chisigma[chi][i] for chi in chisigma])
                    for i in range(len(rr))]))
        lprint('\n')
    return chisigma

# F symbol2c, symbol2b, symbol2d needed for dimBu


def symbol2c(dblpart):
    a, b = dblpart[0][:], dblpart[1][:]
    if len(a) > len(b) + 1:
        b.extend((len(a) - len(b) - 1) * [0])
    elif len(b) + 1 > len(a):
        a.extend((len(b) - len(a) + 1) * [0])
    a.sort()
    b.sort()
    for i in range(1, len(a)):
        a[i] += 2 * i
        b[i - 1] += 2 * i - 1
    return [a, b]


def symbol2b(dblpart):
    a, b = dblpart[0][:], dblpart[1][:]
    if len(a) > len(b) + 1:
        b.extend((len(a) - len(b) - 1) * [0])
    elif len(b) + 1 > len(a):
        a.extend((len(b) - len(a) + 1) * [0])
    a.sort()
    b.sort()
    for i in range(1, len(b)):
        a[i] += 2 * i
        b[i] += 2 * i
    a[-1] = a[-1] + 2 * len(b)
    return [a, b]


def symbol2d(dblpart):
    a, b = dblpart[0][:], dblpart[1][:]
    if len(a) > len(b):
        b.extend((len(a) - len(b)) * [0])
    elif len(b) > len(a):
        a.extend((len(b) - len(a)) * [0])
    a.sort()
    b.sort()
    for i in range(1, len(b)):
        a[i] += 2 * i
        b[i] += 2 * i
    return [a, b]

# F dimBu


def dimBu(W):
    """returns, for every irreducible character of a  finite Weyl group, the
    dimension of the variety of Borel subgroups containing an  element in
    the unipotent class corresponding to that character via the  Springer
    correspondence (where the underlying algebraic group is defined  over
    a field of characteristic p where either p=0 or p is a good prime.)

    >>> W = coxeter("G", 2)
    >>> dimBu(W); chartable(W)['a']; chartable(W)['b']
    [0, 6, 1, 3, 1, 2]
    [0, 6, 1, 1, 1, 1]
    [0, 6, 3, 3, 1, 2]

    This uses  the explicit  knowledge of the  Springer correspondence in
    all cases, as determined by Springer (1977) for A_n, G_2; Shoji (1979)
    and  Lusztig (1984)  for B_n, C_n, D_n;  Shoji (1980)  for F_4;  Alvis-
    Lusztig (1982) and Spaltenstein (1982) for E_6, E_7, E_8.

    Note that the function yields different results for B_n and C_n:

    >>> dimBu(coxeter("B", 3))
    [4, 3, 4, 9, 1, 2, 1, 5, 0, 2]
    >>> dimBu(coxeter("C", 3))
    [6, 3, 4, 9, 2, 2, 1, 4, 0, 1]

    See also 'chartable' and 'inductiontable'.
    """
    db = []
    for ct in W.cartantype:
        if ct[0] == 'A':
            db.append(chartable(coxeter('A', len(ct[1])), chars=False)['a'])
        if (ct[0] == 'B' or ct[0] == 'C') and len(ct[1]) == 2:
            db.append([2, 1, 4, 0, 1])
        if ct[0] == 'B' and len(ct[1]) > 2:
            d = []
            for param in partitiontuples(len(ct[1]), 2):
                symb = symbol2b(param)
                x = 0
                for i in range(len(symb[0])):
                    for j in range(len(symb[0])):
                        if i < j:
                            x += symb[0][i]
                            if j < len(symb[1]):
                                x += symb[1][i]
                        if j < len(symb[1]):
                            if symb[0][i] <= symb[1][j]:
                                x += symb[0][i]
                            else:
                                x += symb[1][j]
                d.append(x - len(symb[1]) * (4 * len(symb[1]) + 1) * (len(symb[1]) - 1) // 3)
            db.append(d)
        if ct[0] == 'C' and len(ct[1]) > 2:
            d = []
            for param in partitiontuples(len(ct[1]), 2):
                symb = symbol2c(param)
                x = 0
                for i in range(len(symb[0])):
                    for j in range(len(symb[0])):
                        if i < j:
                            x += symb[0][i]
                            if j < len(symb[1]):
                                x += symb[1][i]
                        if j < len(symb[1]):
                            if symb[0][i] <= symb[1][j]:
                                x += symb[0][i]
                            else:
                                x += symb[1][j]
                d.append(x - len(symb[1]) * (4 * len(symb[1]) * len(symb[1]) - 1) // 3)
            db.append(d)
        if ct[0] == 'D':
            d = []
            for mu in partitiontuples(len(ct[1]), 2):
                symb = symbol2d(mu)
                if mu[0] == mu[1] or mu[0] < mu[1]:
                    x = 0
                    for i in range(len(symb[0])):
                        for j in range(len(symb[0])):
                            if i < j:
                                x += symb[0][i] + symb[1][i]
                            if symb[0][i] <= symb[1][j]:
                                x += symb[0][i]
                            else:
                                x += symb[1][j]
                    x -= len(symb[1]) * (len(symb[1]) - 1) * (4 * len(symb[1]) - 5) // 3
                    d.append(x)
                    if mu[0] == mu[1]:
                        d.append(x)
            db.append(d)
        if ct[0] == 'G':
            db.append([0, 6, 1, 3, 1, 2])
        if ct[0] == 'F':
            db.append([0, 9, 4, 24, 2, 13, 1, 16, 6, 2, 6, 4, 10, 6, 4, 4, 1, 7, 5, 13, 3, 9, 3, 9, 5])
        if ct[0] == 'E' and len(ct[1]) == 6:
            db.append([0, 36, 9, 1, 25, 7, 3, 15, 4, 16, 2, 20,
                      6, 12, 3, 15, 8, 7, 7, 5, 11, 4, 13, 6, 10])
        if ct[0] == 'E' and len(ct[1]) == 7:
            db.append([0, 63, 46, 1, 28, 5, 3, 30, 36, 3, 2, 37, 16, 7, 4, 31, 30, 3, 18, 9, 12, 14, 25,
                       4, 6, 21, 12, 15, 4, 25, 6, 21, 8, 15, 22, 5, 20, 7, 6, 21, 10, 13, 16, 9, 16, 7,
                       8, 17, 16, 7, 13, 10, 14, 9, 8, 15, 10, 13, 11, 11])
        if ct[0] == 'E' and len(ct[1]) == 8:
            db.append([0, 120, 3, 63, 2, 74, 16, 5, 56, 4, 64, 21, 10, 36, 4, 52, 20, 6, 42, 8, 32, 12,
                       36, 6, 46, 18, 14, 28, 6, 42, 16, 13, 26, 16, 12, 31, 9, 34, 20, 8, 38, 18, 8,
                       32, 8, 32, 18, 13, 25, 18, 10, 28, 16, 10, 30, 16, 14, 22, 16, 16, 22, 11, 26,
                       12, 24, 14, 22, 1, 91, 7, 37, 3, 63, 4, 52, 17, 7, 43, 9, 39, 5, 47, 19, 10, 28,
                       7, 37, 19, 10, 30, 11, 29, 7, 37, 15, 21, 13, 25, 17, 9, 31, 12, 24, 17, 11, 26,
                       15, 21, 13, 23, 15, 21])
        if db == []:
            print("#W only works for crystallographic types")
    return [sum(di) for di in cartesian(db)]

# F ainvariants


def ainvariants(W, weightL=0):
    """computes  the a-invariants of the irreducible  characters of W with
    respect to a weight function. This is done by a recursive procedure
    based on Def. 4.1 in:

      M. Geck, Some applications of CHEVIE in the theory of algebraic
               groups, Carpath. J. Math. 27 (2011), 64-94.

    It requires the character tables and induction tables corresponding
    to the various parabolic subgroups of W.

    A weight function is given  by a sequence of non-negative  integers
    corresponding to the  simple reflections of W,  where  weights  for
    simple reflections  which are conjugate in W have to be equal. This
    gives rise to a weight function  L  from  W to the integers  in the
    sense of Lusztig; given w in W, we have

         L(w) = weightL[s_1] + weightL[s_2] + ... + weightL[s_k]

    where w=(s_1, ..., s_k) is a reduced expression for w.  It is allowed
    that weightL is just an integer, in which case all weights will  be
    set  equal to that integer.  The default value for weightL is 0, in
    which case all the a-invariants are equal to 0.

    In the case where all weights are equal to 1, the  a-invariants are
    given  by the  order of vanishing of the generic degrees associated
    with  the  irreducible characters of W;  in this special case,  the
    a-invariants are already  contained as one component in the  result
    of 'chartable' (and we use this information here).

    See also 'chartable', 'constructible' and 'lusztigfamilies'.

    >>> W = coxeter("B", 3)
    >>> ainvariants(W, 1)            # all weights equal to 1
    [4, 3, 4, 9, 1, 2, 1, 4, 0, 1]
    >>> ainvariants(W, [3, 2, 2, 2])    # weights [3, 2, 2, 2]
    [7, 6, 10, 21, 2, 5, 3, 11, 0, 4]
    >>> ainvariants(W, [0, 1, 1, 1])    # weights [0, 1, 1, 1]
    [6, 3, 3, 6, 2, 1, 1, 2, 0, 0]
    """
    cw = conjugacyclasses(W)['reps']
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL
    if all(p == 0 for p in poids):
        return len(cw) * [0]
    if len(set(poids)) == 1:
        return [poids[0] * i for i in chartable(W, chars=False)['a']]
    gens = [j for j in range(len(cw)) if len(cw[j]) == 1]
    ti = chartable(W)
    irr = ti['irreducibles']
    omega = [sum(ti['classlengths'][s] * irr[t][s] * poids[cw[s][0]]
                 for s in gens) // irr[t][0] for t in range(len(cw))]
    tainv = len(irr) * [0]
    for s in W.rank:
        J = list(W.rank)
        J.remove(s)
        H = reflectionsubgroup(W, J)
        t = inductiontable(H, W)
        ainvH = ainvariants(H, [poids[j] for j in J])
        for i in range(len(t['charW'])):
            for j in range(len(t['charH'])):
                if t['scalar'][i][j] != 0 and ainvH[j] > tainv[i]:
                    tainv[i] = ainvH[j]
    ainv = len(irr) * [0]
    for t in range(len(irr)):
        if tainv[ti['permsgn'][t]] - tainv[t] <= omega[t]:
            ainv[t] = tainv[t]
        else:
            ainv[t] = tainv[ti['permsgn'][t]] - omega[t]
    return ainv

# F niceprintconstructible


def niceprintconstructible(cnst, chn):
    if len(cnst) == 1:
        lprint('# one constructible character:\n')
    else:
        lprint('# ' + str(len(cnst)) + ' constructible characters:\n')
    for x in cnst:
        lprint('# ')
        z = 0
        for i in range(len(x)):
            if x[i] != 0:
                if z == 1:
                    lprint(' + ')
                if x[i] != 1:
                    lprint(str(x[i]) + '*')
                if len(chn[i]) == 1:
                    lprint(chn[i][0])
                else:
                    lprint(str(chn[i]))
                z = 1
        lprint('\n')

# F constructible


def constructible(W, weightL=1, display=True):
    """computes the constructible characters of W as defined by

      G. Lusztig, A class of irreducible representations of a finite
                  Weyl group II, Indag. Math. 44 (1982), 219-226.

    The result is a dictionary with components:

    'constructibles' :  the matrix containing the multiplicities of the
        various irreducible characters in the constructible characters.

    'families'       : the partition of Irr(W) into families.

    The constructible characters are computed by a recursive procedure,
    using induction of characters from parabolic subgroups,  truncation
    by a-invariants and tensoring with the sign character.

    In the equal parameter case (where weightL=1, default value), these
    are known  to be  equal  to the  characters afforded by the various
    Kazhdan-Lusztig left cells of W.  The definition and the  algorithm
    also make sense for general weightL,  but then the  connection with
    cells is still conjectural.

    If the optional argument 'display' is set to False, then  the  step
    of  printing a  formatted list  of the  constructible characters is
    skipped.

    See also 'ainvariants' and 'lusztigfamilies'.

    >>> W = coxeter("B", 2)
    >>> constructible(W)             # equal parameter case
    # 4 constructible characters:
    # [[2], []]
    # [[1], [1]] + [[], [2]]
    # [[1, 1], []] + [[1], [1]]
    # [[], [1, 1]]
    {'constructibles':
       [[0, 0, 0, 1, 0], [0, 1, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 1, 0, 0]],
     'families': [[3], [0, 1, 4], [2]]}

    >>> constructible(W, [1, 2])       # unequal parameters
    # 5 constructible characters:
    # [[2], []]
    # [[1, 1], []]
    # [[1], [1]]
    # [[], [2]]
    # [[], [1, 1]]
    {'constructibles': [[0, 0, 0, 1, 0], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0],
                        [0, 0, 0, 0, 1], [0, 0, 1, 0, 0]],
     'families': [[3], [0], [1], [4], [2]]}

    >>> constructible(W, [1, 0])       # unequal parameters
    # 3 constructible characters:
    # [[2], []] + [[], [2]]
    # [[1], [1]]
    # [[1, 1], []] + [[], [1, 1]]
    {'constructibles': [[0, 0, 0, 1, 1], [0, 1, 0, 0, 0], [1, 0, 1, 0, 0]],
     'families': [[3, 4], [1], [0, 2]]}

    >>> c=constructible(coxeter("F", 4))
    # 17 constructible characters:
    # 1_1
    # 2_3 + 4_2
    # 2_1 + 4_2
    # 9_1
    # 8_1
    # 8_3
    # 9_3 + 6_1 + 12 + 4_4 + 16
    # 9_2 + 6_1 + 12 + 4_3 + 16
    # 4_1 + 9_2 + 9_3 + 6_2 + 12 + 2*16
    # 1_3 + 2*9_3 + 6_2 + 12 + 4_4 + 16
    # 1_2 + 2*9_2 + 6_2 + 12 + 4_3 + 16
    # 8_2
    # 8_4
    # 9_4
    # 2_4 + 4_5
    # 2_2 + 4_5
    # 1_4
    """
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL
    if len(W.rank) == 0:
        return {'constructibles': [[1]], 'families': [[0]]}
    # if len(W.rank)==1:
    #  if poids[0]==0:
    #    return [[1, 1]]
    #  else:
    #    return [[1, 0], [0, 1]]
    ti = chartable(W)
    ag = ainvariants(W, poids)
    const = []
    for s in W.rank:
        J = list(W.rank)
        J.remove(s)
        H = reflectionsubgroup(W, J)
        it = inductiontable(H, W)['scalar']
        poidsJ = [poids[j] for j in J]
        au = ainvariants(H, poidsJ)
        for i in range(len(au)):
            for j in range(len(ag)):
                if ag[j] != au[i]:
                    it[j][i] = 0
        for x in matmult(constructible(H, poidsJ,
                     display=False)['constructibles'], transposemat(it)):
            if x not in const:
                const.append(x[:])
            nx = len(x) * [0]
            for i in range(len(nx)):
                nx[ti['permsgn'][i]] = x[i]
            if nx not in const:
                const.append(nx[:])
    const.sort()
    rest = list(range(len(ag)))
    f = []
    while rest != []:
        o = [rest[0]]
        for chi in o:
            for cp in const:
                for psi in range(len(ag)):
                    if cp[chi] != 0 and cp[psi] != 0 and psi not in o:
                        o.append(psi)
        o.sort()
        f.append(o[:])
        for x in o:
            rest.remove(x)
    f.sort(key=(lambda x: ag[x[0]]))
    fam = []
    for c in const:
        i = 0
        while c[i] == 0:
            i += 1
        j = 0
        while i not in f[j]:
            j += 1
        fam.append(j)
    nconst = []
    for i in range(len(f)):
        for c in range(len(const)):
            if fam[c] == i:
                nconst.append(const[c])
    if display:
        niceprintconstructible(nconst, ti['charnames'])
    return {'constructibles': nconst, 'families': f}


def lusztigpreceq(W, poids, display=False):
    """returns the incidence matrix needed for determining families
    and  the  pre-order relation on them;  see 'lusztigfamilies'
    for further details.
    """
    ti = chartable(W)
    if len(W.rank) == 0:
        return [[True]]
    if len(W.rank) == 1:
        if poids == [0]:
            return [[True, True], [True, True]]
        else:
            if ti['position_id'] < ti['position_sgn']:
                return [[True, True], [False, True]]
            else:
                return [[True, False], [True, True]]
    ag = ainvariants(W, poids)
    fam = [[False for j in range(len(ag))] for i in range(len(ag))]
    for s in W.rank:
        if display:
            lprint('.')
        J = list(W.rank)
        J.remove(s)
        H = reflectionsubgroup(W, J)
        it = inductiontable(H, W)['scalar']
        poidsJ = [poids[j] for j in J]
        au = ainvariants(H, poidsJ)
        fam1 = lusztigpreceq(H, poidsJ)
        for psi1 in range(len(au)):
            for psi2 in range(len(au)):
                if fam1[psi1][psi2]:
                    for chi1 in filter(lambda i: ag[i] == au[psi1] and
                                       it[i][psi1] != 0, range(len(ag))):
                        for chi2 in filter(lambda j: it[j][psi2] != 0,
                                           range(len(ag))):
                            fam[chi1][chi2] = True
                            fam[ti['permsgn'][chi2]][ti['permsgn'][chi1]] = True
        for chi in range(len(ag)):  # transitive closure
            orb = [chi]
            for chi1 in orb:
                for chi2 in range(len(ag)):
                    if fam[chi1][chi2] and chi2 not in orb:
                        orb.append(chi2)
            for chi1 in orb:
                fam[chi][chi1] = True
    return fam


# F lusztigfamilies
def lusztigfamilies(W, weightL=1, verbose=False):
    """returns the partition of the set of irreducible characters of W
    into families, as defined in Chapter 4 of:

      G. Lusztig, Characters of reductive groups over a finite field
                  (Princeton University Press 1984).

    The result is a dictionary with entries:

      'families':       partition of Irr(W) into families
      'names'   :       same with names of the characters
      'ainv'    :       constant values of a-invariants on families
      'hasse'   :       neighboring relations in partial order.

    (See also 'ainvariants'.)  Here, we refer to  the partial order
    on families defined in:

      M. Geck, On the Kazhdan-Lusztig order of cells and families
              (Comm.  Math. Helv. 87, pp. 905--927, 2012).

    The construction  uses a  recursive procedure,  similar to that
    for constructible characters.  (See  also 'constructible'.)  In
    the equal parameter case (where  weightL=1, default value), the
    families and the partial order  are known to  correspond to the
    two-sided  Kazhdan-Lusztig cells and the  natural partial order
    on them.

    >>> lusztigfamilies(coxeter("H", 3))
    {'families': [[1], [6, 7], [3], [8, 9], [2], [4, 5], [0]],
    'names':  [[('1_r',)], [("3_s'",), ("overline{3}_s'",)],
                  [('5_r',)], [("4_r'",), ('4_r',)], [("5_r'",)],
                  [('3_s',), ('overline{3}_s',)], [("1_r'",)]],
    'ainv': [0, 1, 2, 3, 5, 6, 15],
    'hasse': [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 6]]}

    Thus, there are 7 families in this case, and the partial  order
    is a linear order.

    >>> W = coxeter("B", 2)
    >>> lusztigfamilies(W)      # equal parameters
    {'families': [[3], [0, 1, 4], [2]],
    'names':  [[('[[2], []]',)], [('[[1, 1], []]',), ('[[1], [1]]',),
                  ('[[], [2]]',)], [('[[], [1, 1]]',)]],
    'ainv': [0, 1, 4],
    'hasse': [[0, 1], [1, 2]]}

    >>> lusztigfamilies(W, [2, 1])
    {'families': [[3], [0], [1], [4], [2]],
    'names': [[('[[2], []]',)], [('[[1, 1], []]',)], [('[[1], [1]]',)],
                 [('[[], [2]]',)], [('[[], [1, 1]]',)]]
    'ainv': [0, 1, 2, 3, 6],
    'hasse': [[0, 1], [1, 2], [2, 3], [3, 4]]}
    """
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL
    ti = chartable(W)
    if len(W.rank) == 0:
        return {'hasse': [], 'ainv': [0],
                'families': [[0]], 'names': [['[1]']]}
    if len(W.rank) == 1:
        if poids[0] == 0:
            return {'hasse': [], 'ainv': [0], 'families': [[0, 1]],
                    'names': [['[1, 1]', '[2]']]}
        else:
            return {'hasse': [[0, 1]], 'ainv': [0, 1], 'families': [[1], [0]],
                    'names': [['[2]'], ['[1, 1]']]}

    ag = ainvariants(W, poids)
    if verbose:
        lprint('#I ')
    fam = lusztigpreceq(W, poids, display=True)
    check = True
    fam1 = []
    rest = list(range(len(ag)))
    while rest:
        chi = rest[0]
        orb = [chi]
        for chi1 in range(1, len(rest)):
            if fam[chi][rest[chi1]] and fam[rest[chi1]][chi]:
                orb.append(rest[chi1])
        fam1.append(orb[:])
        if len(set([ag[x] for x in orb])) > 1:
            check = False
        for o in orb:
            rest.remove(o)
    fam1.sort(key=(lambda i: ag[i[0]]))
    rest = []
    for chi1 in fam1:
        for chi2 in fam1:
            if chi1 != chi2 and any(any(fam[psi1][psi2]
                                  for psi2 in chi2) for psi1 in chi1):
                rest.append([fam1.index(chi1), fam1.index(chi2)])
    hasse = []
    for chi1 in range(len(fam1)):
        for chi2 in range(len(fam1)):
            if chi1 != chi2 and [chi1, chi2] in rest:
                if not any(chi != chi1 and chi != chi2 and [chi1, chi] in rest
                           and [chi, chi2] in rest for chi in range(len(fam1))):
                    hasse.append([chi1, chi2])
    for h in hasse:
        if ag[fam1[h[0]][0]] > ag[fam1[h[1]][0]]:
            check = False
    if verbose:
        if len(fam1) == 1:
            lprint(' ' + str(len(fam1)) + ' family; ')
        else:
            lprint(' ' + str(len(fam1)) + ' families; ')
            lprint(' monotony of a-function is ' + str(check) + '\n')
    return {'families': fam1, 'ainv': [ag[x[0]] for x in fam1],
            'hasse': hasse,
            'names': [[ti['charnames'][i] for i in f] for f in fam1]}


def poincarepol(W, paramL):
    """returns the  Poincare polynomial  of a finite Coxeter group with
    respect to a list of parameters. This is defined by

                   P_W = sum_{w in W} ind(w)

    where ``ind(w)=paramL[s_1]* ... *paramL[s_k]`` and w=s_1...s_k is a
    reduced expression for w.  The parameters are a list of elements
    in a base ring,  one for each  simple reflection in W, such that
    two  parameters are equal whenever the corresponding reflections
    are conjugate in  W.  For example,  a typical parameter list  is
    given by [u^a, u^b, ...] where [a, b, ...] form a list of weights as
    in 'ainvariants' and u is some indeterminate. It is allowed that
    the argument  paramL  is just  one element,  in  which  case all
    parameters will be set equal to that element; the  default value
    is 1, in which case the function returns the group order.

    >>> W = coxeter("G", 2)
    >>> v = lpol([1], 1, 'v')
    >>> p = poincarepol(W, v); p
    1+2*v+2*v**2+2*v**3+2*v**4+2*v**5+v**6
    >>> from polynomials import cycldec
    >>> cycldec(p)           # factorise into cyclotomic polynomials
    [1, 0, [[2, 2], [3, 1], [6, 1]]]

    See also 'heckechartable'.  (Note that the parameters used there
    are square roots of the parameters used here.)
    """
    if isinstance(paramL, list):
        vs = paramL[:]
    else:
        vs = len(W.rank) * [paramL]
    if len(W.rank) == 0:
        return 1
    else:
        W1 = reflectionsubgroup(W, list(W.rank)[:-1])
        po = poincarepol(W1, vs[:-1])
        rp = 0
        for w in redrightcosetreps(W, W1):
            p = 1
            for s in W.coxelmtoword(w):
                p *= vs[s]
            rp += p
        return po * rp

# F classpolynomials


def classpolynomials(W, paramL, pw):
    """computes the  class polynomials  of  an  element  (given as  a full
    permutation on the roots)  with  respect  to a set  of  parameters.
    This is done by a recursive algorithm  (see  [Ge-Pf, 8.2.3, 8.2.7])
    based on 'testcyclishift'. More precisely, let f_{w, C} be the class
    polynomial for an element w in W and a conjugacy class C of W. Then

     f_{w, C} = 1 if w has minimal length in C;

     f_{w, C'} = 0 if w has minimal length in a class C' not equal to C;

     f_{w, C} = f_{w', C} if w, w' are conjugate by cyclic shift;

     f_{w, C} = paramL[s] f_{sws, C} + (paramL[s]-1) f_{sw, C}

                                 where s in S is such that l(sws)<l(w).

    The parameters are a list of elements in a base ring,  one for each
    simple reflection in W, such that two parameters are equal whenever
    the corresponding reflections  are conjugate in W.  For example,  a
    typical parameter list  is given by  [u^a, u^b, ...]  where [a, b, ...]
    form a list of weights as used in the function 'ainvariants', and u
    is some indeterminate.  It is  allowed  that the argument paramL is
    just one element, in which case all parameters will be set equal to
    that element.

    The class polynomials are used to  compute the  character values of
    Iwahori-Hecke algebras at basis elements  T_w for arbitrary w in W.
    See also 'heckechartable'. (Note that the parameters used there are
    square roots of the parameters used here.)

    The following example is done in sage:

    sage: W = coxeter("A", 3)
    sage: R.<u> = QQ['u']
    sage: classpolynomials(W, [u, u, u], longestperm(W))
    [0, 0, u^2, u^3 - 2*u^2 + u, u^3 - u^2 + u - 1]

    See also 'allclasspolynomials',  especially  if you need the  class
    polynomials for several elements,  or  elements  of  relatively big
    length.
    """
    if isinstance(paramL, list):
        vs = paramL[:]
    else:
        vs = len(W.rank) * [paramL]
    t = testcyclicshift(W, pw)
    if t:
        cp = len(conjugacyclasses(W)['reps']) * [0]
        cp[identifyclasses(W, [W.permtoword(pw)], minrep=True)[0]] = 1
    else:
        cp1 = classpolynomials(W, vs, t[0])
        cp2 = classpolynomials(W, vs, [t[0][i] for i in W.permgens[t[1]]])
        cp = [vs[t[1]] * cp1[i] + (vs[t[1]] - 1) * cp2[i] for i in range(len(cp1))]
    return cp

# F testcyclicshift1


def testcyclicshift1(W, w, pw):
    """returns the cyclic shift orbit of an element together with some
    additional information, for us in 'allclasspolynomials'.
    """
    bahn = [pw[:]]
    cbahn = set([bytes(pw[:len(W.rank)])])
    l = len([i for i in pw[:W.N] if i >= W.N])
    minr = 1
    for b in bahn:
        for s in W.rank:
            nw = tuple([W.permgens[s][b[W.permgens[s][r]]]
                     for r in range(2 * W.N)])
            lnw = len([i for i in nw[:W.N] if i >= W.N])
            cnw = bytes(nw[:len(W.rank)])
            if minr == 1 and lnw < l:
                sxs, s1 = nw[:len(W.rank)], s
                minr = 0
            if lnw == l and cnw not in cbahn:
                bahn.append(nw)
                cbahn.add(cnw)
    # bahn=[b[:len(W.rank)] for b in bahn]
    if minr == 1:
        return [1, bahn, identifyclasses(W, [w], minrep=True)[0]]
    else:
        return [0, bahn, sxs, s1]


# F allclasspolynomials
def allclasspolynomials(W, paramL, maxl=-1, verbose=False):
    """returns the class polynomials for all elements of a finite  Coxeter
    group of length at most maxl. (In many situations, this may be more
    efficient than calling repeatedly 'classpolynomials'.)  If  maxl is
    not specified, then the class polynomials for all elements  will be
    returned. The result is a dictionary with the elements of W as keys
    (given as coxelms) and values given by the class polynomials.

    >>> W = coxeter("I5", 2)
    >>> c=allclasspolynomials(W, v); c
    {(0, 1): [1, 0, 0, 0],
     (1, 8): [0, 0, 0, 1],
     (2, 9): [0, v, -1+v, 0],
     (3, 6): [0, 1, 0, 0],
     (4, 7): [0, 0, 1, 0],
     (5, 2): [0, 1, 0, 0],
     (6, 5): [0, v**2, -v+v**2, -1+v],
     (7, 0): [0, 0, 0, 1],
     (8, 4): [0, 0, 1, 0],
     (9, 3): [0, v, -1+v, 0]}
    >>> sorted([W.coxelmtoword(w) for w in c])
    [[],
     [0],
     [0, 1],
     [0, 1, 0],
     [0, 1, 0, 1],
     [0, 1, 0, 1, 0],
     [1],
     [1, 0],
     [1, 0, 1],
     [1, 0, 1, 0]]

    See also 'classpolynomials' and 'heckecharvalues'.
    """
    if maxl == -1:
        maxlen = W.N
    else:
        maxlen = min(maxl, W.N)
    if isinstance(paramL, (list, tuple)):
        vs = paramL[:]
    else:
        vs = len(W.rank) * [paramL]
    poin = poincarepol(W, v).coeffs
    cl = conjugacyclasses(W)['reps']
    cpmat = []
    cp = len(cl) * [0]
    cp[0] = 1
    cpmat.append({tuple(W.rank): cp})
    cps = {}
    for s in W.rank:
        cp = len(cl) * [0]
        cp[identifyclasses(W, [[s]], minrep=True)[0]] = 1
        cps[W.permgens[s][:len(W.rank)]] = cp
    cpmat.append(cps)
    if verbose and maxlen > 20:
        lprint('#I 0-1-')
    for l in range(1, maxlen):
        if verbose and maxlen > 20:
            lprint(str(l + 1))
        nl = set()
        ol = set(cpmat[l - 1])
        for w in cpmat[l]:
            for s in W.permgens:
                nw = tuple([s[i] for i in w])
                if nw not in ol:
                    nl.add(nw)
            if len(nl) == poin[l + 1]:
                break
        cps = {}
        if verbose and maxlen > 20:
            lprint('-')
        while nl:
            cw = next(iter(nl))
            cw1 = W.coxelmtoword(cw)
            pc1 = W.wordtoperm(cw1)
            t = testcyclicshift1(W, cw1, pc1)
            if t[0] == 1:
                cp = len(cl) * [0]
                cp[t[2]] = 1
            else:
                cp1 = cpmat[l - 1][t[2]]
                cp2 = cpmat[l][tuple([W.permgens[t[3]][i] for i in t[2]])]
                cp = [vs[t[3]] * cp1[i] + (vs[t[3]] - 1) * cp2[i]
                      for i in range(len(cl))]
            for x in t[1]:
                cx = x[:len(W.rank)]
                cps[cx] = cp
                nl.remove(cx)
            if perminverse(pc1) not in t[1]:
                for x in t[1]:
                    cx = perminverse(x)[:len(W.rank)]
                    cps[cx] = cp
                    nl.remove(cx)
        cpmat.append(cps)
    if verbose and maxlen > 20:
        lprint('\n')
    res = {}
    for l in cpmat:
        for x in l:
            res[x] = l[x]
    return res

# F starkey


def starkey(n, u):
    """returns the matrix required by Starkey's Rule (see [Ge-Pf, 9.2.11])
    to  produce  the character table  of the  Iwahori-Hecke  algebra of
    type A.
    """
    W = coxeter("A", n - 1)
    pt = partitions(n)
    cl = [W.order // centraliserpartition(n, p) for p in pt]
    stk = []
    for mu in range(len(pt)):
        J = list(range(n))
        l = 0
        for i in pt[mu]:
            l += i
            J.remove(l - 1)
        H = reflectionsubgroup(W, J)
        ch = conjugacyclasses(H)
        nam = [partitions(len(t[1]) + 1) for t in H.cartantype]
        fus = []  # more efficient than fusionconjugacyclasses
        for st in cartesian(nam):
            p = flatlist(st)
            p.sort(reverse=True)
            while sum(p) < n:
                p.append(1)
            fus.append(pt.index(p))
        H.fusions[W.cartanname]['classes'] = fus[:]
        neu = inducedchar(W, H, len(ch['reps']) * [1])
        for i in range(len(pt)):
            if neu[i] != 0:
                for j in pt[i]:
                    neu[i] *= sum(u**k for k in range(j))
                neu[i] *= (u - 1)**(len(pt[i]) - len(pt[mu])) * cl[i]
        stk.append(neu[:])
    return transposemat(stk)

# F heckevalueB


def heckevalueB(n, q, Q, gamma, pi):
    """returns  a character value of the generic Iwahori-Hecke algebra
    of type  B_n.  Here,  gamma and pi are bipartitions labelling a
    conjugacy class  and  an  irreducible character,  respectively.
    (This function is taken from the gap-chevie library.)  It works
    quite efficiently even for large values of n.

    In particular, the commands:

      >>> p = list(partitiontuples(n, 2))    # not tested
      >>> [[heckevalueB(n, q, Q, a, b) for b in p] for a in p]    # not tested

    will yield the complete character table (with the same ordering
    of the rows and columns as in 'heckechartable'). If q, Q are set
    equal to 1,  then  'heckevalueB' yields an individual  entry of
    the ordinary character table of W(B_n).

    >>> heckevalueB(20, v**2, v**3, [[8, 6, 2], [2, 2]], [[4, 4, 4], [4, 4]])
    -30*v**24+324*v**26-1620*v**28+4500*v**30-7719*v**32+8499*v**34-5940*v**36+2778*v**38-1608*v**40+1590*v**42-1050*v**44+210*v**46+141*v**48-93*v**50+18*v**52
    >>> heckevalueB(20, 1, 1, [[8, 6, 2], [2, 2]], [[4, 4, 4], [4, 4]])
    0

    The whole table for n=20 has 24842 rows and columns.

    See also 'chartableB' and 'heckechartable'.
    """
    if n == 0:
        return q**0
    val = 0 * q
    if pi[0] != []:
        k = pi[0][0]
        for alpha in partitiontuples(n - k, 2):
            dif = [differencepartitions(gamma[0], alpha[0]),
                   differencepartitions(gamma[1], alpha[1])]
            if dif[0] is not False and dif[1] is not False:
                dif = {'cc': dif[0]['cc'] + dif[1]['cc'],
                       'll': dif[0]['ll'] + dif[1]['ll']}
                val += (q - 1)**(dif['cc'] - 1) * (-1)**(dif['ll']) * q**(k - dif['ll'] -
                        dif['cc']) * heckevalueB(n - k, q, Q, alpha,
                            [[pi[0][i] for i in range(1, len(pi[0]))], pi[1]])
    else:
        k = pi[1][0]
        nn = sum(gamma[0])
        if nn >= k:
            for alpha in partitions(nn - k):
                dif = differencepartitions(gamma[0], alpha)
                if dif is not False and dif['cc'] == 1:
                    val += Q * (-1)**(dif['ll']) * q**(n + dif['d']) * heckevalueB(n - k, q, Q,
                      [alpha, gamma[1]], [pi[0], [pi[1][i] for i in range(1, len(pi[1]))]])
        nn = sum(gamma[1])
        if nn >= k:
            for alpha in partitions(nn - k):
                dif = differencepartitions(gamma[1], alpha)
                if dif is not False and dif['cc'] == 1:
                    val += (-1)**(dif['ll'] + 1) * q**(n + dif['d']) * heckevalueB(n - k, q, Q,
                      [gamma[0], alpha], [pi[0], [pi[1][i] for i in range(1, len(pi[1]))]])
    return val


def heckeB(n, q, Q):
    p = list(partitiontuples(n, 2))
    return [[heckevalueB(n, q, Q, a, b) for b in p] for a in p]


def heckeD(n, v):
    W1 = coxeter("B", n)
    r1 = reflections(W1)
    W = reflectionsubgroup(W1, list(range(1, n)) +
                   [r1.index(W1.wordtoperm([0, 1, 0]))])
    cw = conjugacyclasses(W)['reps']
    cc = [i for i in range(len(cw)) if set(cw[i]) == set(list(range(n)))]
    cw1 = [W.reducedword(cw[i], W1) for i in cc]
    if all(len(conjtomin(W1, W1.wordtoperm(x))) == len(x) for x in cw1):
        fus = identifyclasses(W1, cw1, minrep=True)
    else:
        print("Mist!")
        return False
    pt = list(partitiontuples(n, 2))
    t1 = []   # table of restrictions
    for i in range(len(pt)):
        mu = pt[i]
        if mu[0] == mu[1]:
            vals = [divmod(heckevalueB(n, v**2, 1, mu, pt[j]), 2)[0] for j in fus]
            t1.append(vals)
            t1.append(vals)
        elif mu[0] < mu[1]:
            vals = [heckevalueB(n, v**2, 1, mu, pt[j]) for j in fus]
            t1.append(vals)
    tr = transposemat(t1)
    s = len(W.rank)
    while len(cc) < len(cw):     # add non-cuspidal classes
        s -= 1
        J = list(W.rank)
        J.remove(s)
        W1 = reflectionsubgroup(W, J)
        fus = fusionconjugacyclasses(W1, W)
        ind = inductiontable(W1, W)['scalar']
        nti1 = heckechartable(W1, v)['irreducibles']
        for c in fus:
            if c not in cc:
                tr.append([sum(i[j] * nti1[j][fus.index(c)]
                              for j in range(len(nti1))) for i in ind])
                cc.append(c)
    # fint=transposemat([tr[cc.index(i)] for i in range(len(cc))])
    # fint1=[[evalpol(f, 1) for f in l] for l in fint]
    # return [fint[fint1.index(c)] for c in chartable("D", n)['irreducibles']]
    return transposemat([tr[cc.index(i)] for i in range(len(cc))])

# F heckeirrdata


def heckeirrdata(typ, n, paramL):
    """returns a table of raw data for the computation of the character
    table of the  Iwahori-Hecke algebra of type 'typ' and  rank 'n',
    with parameters given by 'paramL'.  More precisely, the function
    returns a triple  [cc, ch, t1] where cc is a list of indices for
    conjugacy classes,  ch is a list of indices  for characters, and
    t1 is the matrix of the corresponding character values. The data
    are extracted from the corresponding files in  gap-chevie.  From
    these data, the complete character table can  be computed  using
    some standard procedures:

    * restriction to parabolic subalgebras (see [Ge-Pf, 9.1.9]),
    * taking dual characters (see [Ge-Pf, 9.4.1]),
    * only in  types A, D, E, H:  taking roots of the longest element
      in the braid group (see [Ge-Pf, 9.2.8]);

    these procedures are performed in the function 'heckechartable'.

    In this way, even for example in type E_8, we only need to store
    a table  of polynomials  of size  18x65 (instead of 112x112); in
    type A, nothing needs to be stored:  the whole table is computed
    using the above procedures.
    """
    if typ[0] == 'A' and n == 0:
        cc = [0]    # list of classes which are stored
        ch = [0]    # list of characters which are stored
        t1 = [[1]]
    if typ[0] == 'A' and n >= 1:
        # v=paramL[0]
        # cl=[centraliserpartition(n+1, p) for p in partitions(n+1)]
        # sti=starkey(n+1, paramL[0])
        # cc=list(range(len(cl)))
        # ch=cc[:]
        # t=chartable(coxeter("A", n))['irreducibles']
        # t1=[[sum(t[i][k]*sti[k][j] for k in range(len(cl)))//cl[0]
        #                for j in range(len(cl))] for i in range(len(cl))]
        cc = []
        ch = []
        t1 = [[]]
    if typ[0] == 'B' and n == 2:
        v = paramL[0]**2
        u = paramL[1]**2  # v == u
        cc = [2, 4]
        ch = [0, 1, 2, 3, 4]
        t1 = [[u**2, -u], [-2 * v * u, 0], [1, 1], [v**2 * u**2, v * u], [v**2, -v]]
    if typ[0] == 'C' and n == 2:   # u == v
        v = paramL[0]**2
        u = paramL[1]**2  # u == v
        cc = [2, 4]
        ch = [0, 1, 2, 3, 4]
        t1 = [[v**2, -v], [-2 * v * u, 0], [1, 1], [v**2 * u**2, v * u], [u**2, -u]]
    if (typ[0] == 'B' or typ[0] == 'C') and n >= 3:
        v = paramL[0]**2
        u = paramL[1]**2  # v == u -- u -- ... --- u
        p = list(partitiontuples(n, 2))
        cc = [i for i in range(len(p)) if p[i][0] == []]
        ch = list(range(len(p)))
        t1 = [[heckevalueB(n, u, v, a, p[b]) for b in cc] for a in p]
    if typ[0] == 'D' and n >= 3:
        v = paramL[0]
        if n == 3 or n == 4:
            cc = []
            ch = []
            t1 = [[]]
        else:
            W1 = coxeter("B", n)
            r1 = reflections(W1)
            W = reflectionsubgroup(W1, list(range(1, n)) +
                           [r1.index(W1.wordtoperm([0, 1, 0]))])
            cw = conjugacyclasses(W)['reps']
            cc = [i for i in range(len(cw)) if set(cw[i]) == set(list(range(n)))]
            cw1 = [W.reducedword(cw[i], W1) for i in cc]
            if n < 11 or all(len(conjtomin(W1, W1.wordtoperm(x))) == len(x) for x in cw1):
                fus = identifyclasses(W1, cw1, minrep=True)
            else:
                print("Mist!")
                return False
            pt = list(partitiontuples(n, 2))
            t1 = []   # table of restrictions
            for i in range(len(pt)):
                mu = pt[i]
                if mu[0] == mu[1]:
                    vals = [divmod(heckevalueB(n, v**2, 1, mu, pt[j]), 2)[0]
                            for j in fus]
                    t1.append(vals)
                    t1.append(vals)
                elif mu[0] < mu[1]:
                    vals = [heckevalueB(n, v**2, 1, mu, pt[j]) for j in fus]
                    t1.append(vals)
            ch = list(range(len(t1)))
    if typ[0] == 'G':
        u = paramL[0]**2
        v = paramL[1]**2   # u === v
        squv = paramL[0] * paramL[1]
        cc = [3, 4, 5]
        ch = [0, 1, 2, 3, 4, 5]
        t1 = [[v * u, v**2 * u**2, v**3 * u**3], [1, 1, 1], [-v, v**2, -v**3], [-u, u**2, -u**3],
            [squv, -v * u, -2 * squv**3], [-squv, -v * u, 2 * squv**3]]
    if typ[0] == 'F':
        u = paramL[0]**2
        v = paramL[2]**2  # u -- u == v -- v
        cc = [i - 1 for i in [2, 5, 6, 8, 9, 10, 11, 24, 25]]
        ch = [i - 1 for i in [1, 2, 5, 7, 9, 10, 11, 14, 15, 16, 17, 18, 21, 23, 25]]
        t1 = [[v**12 * u**12, v**6 * u**4, v**6 * u**6, v**4 * u**6, v**8 * u**8, v**4 * u**4,
             v**2 * u**2, v**7 * u**7, v**3 * u**3],
            [u**12, u**4, u**6, u**6, u**8, u**4, u**2, -u**7, -u**3],
            [2 * v**6 * u**12, 2 * v**3 * u**4, 2 * v**3 * u**6, -v**2 * u**6,
             -v**4 * u**8, -v**2 * u**4, -v * u**2, -v**3 * u**7 + v**4 * u**7, 0],
            [2 * v**12 * u**6, -v**6 * u**2, 2 * v**6 * u**3, 2 * v**4 * u**3,
             -v**8 * u**4, -v**4 * u**2, -v**2 * u, -v**7 * u**3 + v**7 * u**4, 0],
            [4 * v**6 * u**6, -2 * v**3 * u**2, 4 * v**3 * u**3, -2 * v**2 * u**3, v**4 * u**4,
             v**2 * u**2, v * u, v**3 * u**3 - v**3 * u**4 - v**4 * u**3 + v**4 * u**4, 0],
            [9 * v**8 * u**8, 0, -3 * v**4 * u**4, 0, 0, 0, 0, v**4 * u**5 + v**5 * u**4 - v**5 * u**5,
             -v**2 * u**2],
            [9 * v**4 * u**8, 0, -3 * v**2 * u**4, 0, 0, 0, 0, -v**2 * u**4 + v**2 * u**5 - v**3 * u**5,
             v * u**2],
            [6 * v**6 * u**6, v**2 * u**2 - 2 * v**3 * u**2 + v**4 * u**2, 2 * v**3 * u**3,
             v**2 * u**2 - 2 * v**2 * u**3 + v**2 * u**4, 3 * v**4 * u**4, 3 * v**2 * u**2, -v * u,
             -v**3 * u**4 - v**4 * u**3, 0],
            [6 * v**6 * u**6, v**2 * u**2 - 2 * v**3 * u**2 + v**4 * u**2, 2 * v**3 * u**3,
             v**2 * u**2 - 2 * v**2 * u**3 + v**2 * u**4, 3 * v**4 * u**4, 3 * v**2 * u**2, -v * u,
             v**3 * u**3 + v**4 * u**4, 0],
            [12 * v**6 * u**6, -v**2 * u**2 + 2 * v**3 * u**2 - v**4 * u**2, 4 * v**3 * u**3,
             -v**2 * u**2 + 2 * v**2 * u**3 - v**2 * u**4, -3 * v**4 * u**4, -3 * v**2 * u**2, v * u,
             v**3 * u**3 - v**3 * u**4 - v**4 * u**3 + v**4 * u**4, 0],
            [-4 * v**9 * u**9, -2 * v**4 * u**3 + v**5 * u**3, 0, -2 * v**3 * u**4 + v**3 * u**5,
             -2 * v**6 * u**6, 2 * v**3 * u**3, 0, -2 * v**5 * u**5, 0],
            [-4 * v**3 * u**9, v * u**3 - 2 * v**2 * u**3, 0, -2 * v * u**4 + v * u**5, -2 * v**2 * u**6,
             2 * v * u**3, 0, 2 * v**2 * u**5, 0],
            [-8 * v**6 * u**9, -v**2 * u**3 - v**4 * u**3, 0, 2 * v**2 * u**4 - v**2 * u**5,
             2 * v**4 * u**6, -2 * v**2 * u**3, 0, 0, 0],
            [-8 * v**9 * u**6, 2 * v**4 * u**2 - v**5 * u**2, 0, -v**3 * u**2 - v**3 * u**4,
             2 * v**6 * u**4, -2 * v**3 * u**2, 0, 0, 0],
            [-16 * v**6 * u**6, v**2 * u**2 + v**4 * u**2, 0, v**2 * u**2 + v**2 * u**4,
             -2 * v**4 * u**4, 2 * v**2 * u**2, 0, 0, 0]]
    if typ[0] == "E" and n == 6:
        v = paramL[0]
        cc = [11]
        ch = [i - 1 for i in [1, 3, 4, 6, 7, 9, 11, 13, 15, 17, 18, 19, 20, 22, 24]]
        t1 = [[v**28], [-v**16 + 2 * v**14 - v**12], [-2 * v**22], [-2 * v**14],
            [v**20 + v**16], [v**20], [-v**22 + 2 * v**20], [v**18 - 2 * v**16],
            [-v**16], [-v**16 + 2 * v**14 - v**12], [v**16 + v**12],
            [-v**16 + 2 * v**14 - v**12], [-2 * v**16 + v**14], [0], [0]]
    if typ[0] == "E" and n == 7:
        v = paramL[0]
        cc = [i - 1 for i in [36, 38, 39, 44, 47, 54, 59, 60]]
        ch = [i - 1 for i in [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37,
            39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59]]
        t1 = [[v**62, v**46, v**66, v**30, v**50, v**34, v**22, v**26],
            [-v**6 + 5 * v**10, -v**6 + 2 * v**8, 3 * v**10, 2 * v**6, 2 * v**8, v**6, 0, -v**4],
            [5 * v**18 - 5 * v**22, -v**14 + 4 * v**16, -3 * v**22 + 2 * v**24, 0, 2 * v**16 - v**18,
             -v**12, -v**8, 0],
            [10 * v**42 - 5 * v**46 + v**50, v**30 - 2 * v**32 + v**34, 3 * v**46 + 2 * v**48, v**18,
             3 * v**34, v**24, -v**16, v**18],
            [v**10 + 5 * v**18, 2 * v**10 - 2 * v**12, v**18, v**6, v**10 - 2 * v**12, -v**10,
             v**6, v**6],
            [9 * v**46, 0, 3 * v**50, 2 * v**22, 0, -v**26, 0, -v**20],
            [5 * v**22 - 10 * v**26 + 10 * v**30, v**18 + 2 * v**20 - v**22, 6 * v**28 + v**30,
             0, v**18 + 2 * v**24, v**16, v**10, 0],
            [5 * v**46, 2 * v**32, -3 * v**46 + 2 * v**48, 0, -v**34, v**24, -v**16, 0],
            [v**12 + 10 * v**20, v**12 + v**16, 0, v**12, -2 * v**16, 0, 0, v**8],
            [v**18 + 5 * v**26 - 16 * v**28 + 5 * v**30, 3 * v**18 - 4 * v**20 + 2 * v**22,
             2 * v**30, 0, -2 * v**20 + v**22, 0, -v**10, 0],
            [10 * v**30 - 16 * v**32, v**22 + 2 * v**26, 4 * v**36, -v**18,
             -2 * v**26 + v**30, 0, v**12, -v**14],
            [-v**14 + 16 * v**24, -2 * v**14 - v**18, 3 * v**22 + 2 * v**24, 0,
             -v**14 + 2 * v**18, -v**12, -v**8, 0],
            [-16 * v**36 + 15 * v**38 + v**46, 2 * v**26 - 2 * v**28 + 3 * v**30, -3 * v**42,
             0, v**30 + v**34, -v**22, 0, 0],
            [5 * v**30 - 16 * v**32 + 10 * v**34 + v**42, 3 * v**22 - 2 * v**24 + 2 * v**26,
             -3 * v**34, 0, v**22 + v**26, -v**18, 0, 0],
            [16 * v**38 - 5 * v**40 + 5 * v**44 - v**48, -v**28 + 4 * v**30 - 3 * v**32, 0, 0,
             -3 * v**32 + 2 * v**34 - v**36, 0, 0, 0],
            [5 * v**34 + 5 * v**38 - 5 * v**42 + v**46, v**26 - 6 * v**28 + 2 * v**30, 0,
             -2 * v**18, 4 * v**30 - 2 * v**32, 0, 0, v**16],
            [9 * v**30, 0, 6 * v**36 + 3 * v**38, -v**14, 0, -v**20, 0, -v**14],
            [9 * v**22, 0, -3 * v**26, -v**14, 0, v**14, 0, -v**10],
            [9 * v**30, 0, -3 * v**26, -v**10, 0, v**14, 0, -v**10],
            [10 * v**34 + 5 * v**38, -2 * v**28 + 2 * v**30, -2 * v**42, 0,
             -2 * v**32 + v**34, 0, v**14, 0],
            [-5 * v**30 - 15 * v**34 + 5 * v**38, -2 * v**22 + 6 * v**24 - v**26, 6 * v**34, 0,
             2 * v**24 - 4 * v**26, 0, 0, 0],
            [-9 * v**32, 0, 0, v**16, 0, 0, 0, v**12],
            [v**18 - 5 * v**22 + 15 * v**26 - 16 * v**28 + 15 * v**30, 4 * v**18 - 6 * v**20 + 3 * v**22,
             0, 0, v**18 - 2 * v**20 + v**22 - 2 * v**24, 0, 0, 0],
            [-15 * v**32 + 16 * v**34 - 5 * v**36 - v**44, -2 * v**24 + 4 * v**26 - 4 * v**28, 0,
             0, -v**28 + 2 * v**30 - v**32, 0, 0, 0],
            [-v**18 + 5 * v**22 - 15 * v**26 + 16 * v**28 - 5 * v**30, -3 * v**18 + 6 * v**20 - 3 * v**22,
             -6 * v**28 + v**30, 0, 2 * v**20 - v**22 + 2 * v**24, -v**16, v**10, 0],
            [-5 * v**28 + 16 * v**30 - 10 * v**32 + 5 * v**36, -3 * v**20 + 4 * v**22 - v**24, 0,
             v**12, -v**20 + 2 * v**22 - 3 * v**24, 0, 0, v**12],
            [-9 * v**26, 0, 6 * v**30, -2 * v**14, 0, 0, 0, v**12],
            [0, 0, -6 * v**36 + 3 * v**38, 0, 0, v**20, 0, 0],
            [5 * v**26 - 5 * v**34, 4 * v**24 - v**26, -4 * v**36, 0, -v**26 + 2 * v**28,
             0, -v**12, 0],
            [-5 * v**25 + 5 * v**29 - 16 * v**31 + 5 * v**33 - 5 * v**37, 2 * v**21 - 8 * v**23 + 2 * v**25,
             0, 2 * v**15, -2 * v**23 + 4 * v**25 - 2 * v**27, 0, 0, -v**13]]
    if typ[0] == 'E' and n == 8:
        v = paramL[0]
        cc = [i - 1 for i in [9, 13, 15, 17, 24, 29, 34, 39, 42, 45, 47, 48, 49, 54, 55, 56, 58, 63]]
        ch = [i - 1 for i in [1, 3, 5, 7, 8, 10, 12, 13, 15, 17, 18, 20, 22, 24, 26, 27, 29, 31, 32,
            34, 35, 37, 39, 40, 42, 43, 45, 47, 48, 50, 51, 53, 54, 56, 57, 59,
            60, 62, 64, 66, 68, 70, 72, 74, 76, 77, 79, 81, 83, 84, 86, 88, 89,
            91, 93, 95, 97, 99, 100, 102, 104, 105, 107, 109, 111]]
        t1 = [[v**128, v**84, v**88, v**132, v**64, v**88, v**92, v**44,
             v**36, v**68, v**32, v**56, v**28, v**92, v**52, v**44, v**48, v**52],
            [15 * v**92 - 6 * v**100 + v**108, v**60 - 6 * v**62 + 6 * v**64,
             6 * v**64 - 8 * v**66 + 3 * v**68, 6 * v**96 + 2 * v**102, 6 * v**44 - 4 * v**48 + v**52,
             3 * v**64 - 4 * v**66 + 3 * v**68, 8 * v**68 - 4 * v**70 + v**72, 2 * v**32 - v**34, 0,
             v**48 + v**50, v**20, v**40, v**20, 3 * v**68 - 2 * v**70 + v**72,
             3 * v**36 - v**42, 3 * v**32 - v**34, v**32 - 2 * v**34 + v**36 - v**38, -v**38 + v**40],
            [20 * v**100 - 6 * v**104, -4 * v**66 + 3 * v**68, 4 * v**68 - 4 * v**70 + 2 * v**72,
             9 * v**104 - 2 * v**108, 5 * v**48, -4 * v**70 + v**72, 4 * v**72 - 2 * v**74 + v**76,
             -2 * v**34, 0, v**52, 2 * v**24, -v**44, -v**22, -2 * v**74, v**44, v**36,
             v**40, -v**40],
            [15 * v**56 - 20 * v**64 + 15 * v**72, 6 * v**40 - 14 * v**42 + 6 * v**44,
             v**40 - 8 * v**42 + 18 * v**44 - 8 * v**46 + v**48, v**60 + 12 * v**66 + v**72,
             v**24 - 4 * v**28 + 6 * v**32 - 4 * v**36 + v**40,
             v**40 - 4 * v**42 + 9 * v**44 - 4 * v**46 + v**48, 8 * v**44 - 10 * v**46 + 8 * v**48,
             v**20 - 2 * v**22 + v**24, 0, v**30 + v**38, -2 * v**16, v**28, v**14,
             3 * v**44 - 4 * v**46 + 3 * v**48, v**20 - 3 * v**26 + v**32, v**20 - 3 * v**22 + v**24,
             v**20 - v**22 + 2 * v**24 - v**26 + v**28, v**24 - 2 * v**26 + v**28],
            [-15 * v**88 + 20 * v**92, -6 * v**58 + 2 * v**60, 8 * v**60 - 4 * v**62 + v**64,
             4 * v**90 - 9 * v**92 + 3 * v**96, 0, v**60 - 4 * v**62, -2 * v**62 + 4 * v**64 - 2 * v**66,
             v**32, v**24, -v**46 + v**50, -v**24, -v**40, -v**20, v**64, v**34,
             v**30, -2 * v**32, 0],
            [15 * v**92 + 6 * v**100, 6 * v**62 - 3 * v**64, -4 * v**64 + 8 * v**66 - v**68,
             2 * v**96 + 2 * v**102, 4 * v**48, -v**64 + 4 * v**66 - v**68, -5 * v**68 + 4 * v**70,
             2 * v**32 - v**34, 0, -v**48 + v**50, 0, 0, 0, -v**68 + 2 * v**70, -v**36 - v**42,
             -v**32 - v**34, 2 * v**34 - v**38, v**38],
            [24 * v**60 - 60 * v**64 + 24 * v**68, 6 * v**40 - 6 * v**42 + 6 * v**44,
             3 * v**40 - 4 * v**42 + 8 * v**44 - 4 * v**46 + 3 * v**48,
             v**60 - 9 * v**64 + 24 * v**66 - 9 * v**68 + v**72, -4 * v**28 + 6 * v**32 - 4 * v**36,
             v**40 + 5 * v**44 + v**48, v**40 + v**44 - 6 * v**46 + v**48 + v**52,
             v**20 - 2 * v**22 + v**24, 0, v**30 - 2 * v**34 + v**38, 0, 0, 0, -4 * v**46,
             v**20 - 3 * v**26 + v**32, v**20 - 3 * v**22 + v**24,
             v**20 - v**22 + 2 * v**24 - v**26 + v**28, -2 * v**26],
            [10 * v**72 - 60 * v**76 + 45 * v**80, v**48 + 12 * v**50,
             v**48 + 4 * v**50 - 10 * v**52 + 8 * v**54 + v**56, 16 * v**78 - 18 * v**80 + v**84, 0,
             -10 * v**52 + 4 * v**54 + v**56, -3 * v**52 + 8 * v**54 - 7 * v**56 + 2 * v**58 + v**60,
             v**24 - 2 * v**26 + v**28, 0, -v**44, v**16, v**32, v**16, 2 * v**54 - 3 * v**56,
             -2 * v**30 + v**36, -2 * v**26 + v**28, -v**26 - v**30 + v**32, 0],
            [64 * v**86 - 30 * v**88 + 6 * v**96 - v**104, -3 * v**56 + 6 * v**58 - 9 * v**60,
             4 * v**58 - 4 * v**60 + 8 * v**62 - 5 * v**64, 12 * v**90 - 9 * v**92 + 3 * v**96, 5 * v**40,
             v**60 + 4 * v**62 - 4 * v**64, -2 * v**62 - 2 * v**64 + 4 * v**66 - 2 * v**68, v**32, 0,
             v**46 - v**50, 0, 0, 0, 2 * v**64 + 2 * v**66 - v**68, -3 * v**34, -3 * v**30,
             -v**30 + 2 * v**32 - v**34, -v**36],
            [60 * v**60 - 150 * v**64 + 60 * v**68, 6 * v**40 - 24 * v**42 + 6 * v**44,
             2 * v**40 - 12 * v**42 + 26 * v**44 - 12 * v**46 + 2 * v**48,
             -18 * v**64 + 48 * v**66 - 18 * v**68, v**24 - 4 * v**28 + 6 * v**32 - 4 * v**36 + v**40,
             -4 * v**42 + 16 * v**44 - 4 * v**46, -2 * v**42 + 8 * v**44 - 16 * v**46 + 8 * v**48 - 2 * v**50,
             0, 0, 0, 0, 0, 0, -6 * v**46, 0, 0, 0, v**24 - 2 * v**26 + v**28],
            [84 * v**80 - 64 * v**82 + 15 * v**84 - 6 * v**92 + v**100,
             6 * v**52 - 18 * v**54 + 15 * v**56, v**52 - 8 * v**54 + 14 * v**56 - 20 * v**58 + 7 * v**60,
             22 * v**84 - 18 * v**86 + 4 * v**90, 0, 9 * v**56 - 8 * v**58 + 5 * v**60,
             3 * v**56 - 4 * v**58 + 10 * v**60 - 8 * v**62 + 2 * v**64, v**26 + v**30, -v**24,
             -v**42 - v**44, 0, 0, 0, 3 * v**60 - 2 * v**62 + v**64, v**32 + v**38,
             v**28 + v**30, -2 * v**30 + v**34, 0],
            [70 * v**72 - 64 * v**78 + 15 * v**80 + 20 * v**84 - 6 * v**88,
             8 * v**48 - 24 * v**50 + 15 * v**52, v**48 - 12 * v**50 + 24 * v**52 - 20 * v**54 + 6 * v**56,
             9 * v**76 + 18 * v**80 - v**84, 0, -4 * v**50 + 8 * v**52 - 12 * v**54 + 3 * v**56,
             7 * v**52 - 8 * v**54 + 13 * v**56 - 6 * v**58 + v**60, -v**24, 0, v**40 - v**44,
             -v**16, -v**32, -v**16, -2 * v**54 + 3 * v**56 - 2 * v**58, -v**36, -v**28,
             -v**32, 0],
            [24 * v**68 + 24 * v**76 - 64 * v**78 + 45 * v**80 + v**96,
             9 * v**48 - 12 * v**50 + 15 * v**52, 2 * v**48 - 8 * v**50 + 14 * v**52 - 12 * v**54 + 7 * v**56,
             v**72 - 9 * v**80 + v**84, 0, v**48 + 4 * v**52 - 4 * v**54 + 5 * v**56,
             2 * v**52 - 4 * v**54 + 4 * v**56 - 4 * v**58 + 2 * v**60, -2 * v**26 + v**28, 0,
             -v**36 + v**40 - v**44, 0, 0, 0, v**56 + v**60, v**24 + v**36, v**24 + v**28,
             v**24 + v**32, 0],
            [81 * v**80, 0, 0, 9 * v**84 + 9 * v**88 - 3 * v**92, 4 * v**36 + 4 * v**44 - v**48,
             0, 0, 0, 0, -2 * v**44 + v**48, 0, 0, 0, -3 * v**60, 0, 0, 0, 2 * v**34 - v**36],
            [15 * v**56 - 64 * v**58 + 84 * v**60 - 70 * v**64 + 84 * v**68 - 64 * v**70 + 15 * v**72,
             27 * v**40 - 54 * v**42 + 27 * v**44,
             9 * v**40 - 36 * v**42 + 54 * v**44 - 36 * v**46 + 9 * v**48,
             2 * v**60 - 9 * v**64 + 44 * v**66 - 9 * v**68 + 2 * v**72,
             v**24 - 4 * v**28 - 4 * v**36 + v**40,
             3 * v**40 - 12 * v**42 + 27 * v**44 - 12 * v**46 + 3 * v**48,
             v**40 - 6 * v**42 + 18 * v**44 - 26 * v**46 + 18 * v**48 - 6 * v**50 + v**52,
             -v**20 + 2 * v**22 - v**24, 0, -2 * v**34, 0, 0, 0, 3 * v**44 - 6 * v**46 + 3 * v**48,
             -v**20 - v**26 - v**32, -v**20 - v**22 - v**24, -v**20 + 2 * v**24 - v**28,
             v**24 - 2 * v**26 + v**28],
            [-24 * v**64 - 60 * v**72 + 64 * v**74, -6 * v**44 + 12 * v**46 - 8 * v**48,
             -v**44 + 12 * v**46 - 8 * v**48 + 8 * v**50 - 4 * v**52,
             2 * v**66 + 14 * v**72 - 18 * v**74 + 2 * v**78, 0, -v**44 - 6 * v**48 + 4 * v**50 - v**52,
             2 * v**46 - 4 * v**48 + 4 * v**50 - v**52 + 2 * v**54 - v**56, -v**22 + 2 * v**24 - 2 * v**26,
             0, -v**36 - v**38, v**20, v**32, v**16, 0, -v**22 + 2 * v**28 - v**34,
             -v**22 + 2 * v**24 - v**26, -v**22 + v**24 + v**28 - v**30, 0],
            [24 * v**80 + 30 * v**84 + v**100, 3 * v**52 - 2 * v**54 + 6 * v**56,
             v**52 + 4 * v**56 - 4 * v**58 + 3 * v**60, -18 * v**84 + 18 * v**86 - 4 * v**90, 0,
             -v**56 + 3 * v**60, -2 * v**56 + 2 * v**60 - 2 * v**62 + v**64, -v**26 - v**30, 0,
             v**42 - v**44, -2 * v**20, v**36, v**18, -2 * v**60 + v**64, 3 * v**32 - v**38,
             3 * v**28 - v**30, v**28 - 2 * v**30 + v**32 - v**34, 0],
            [45 * v**56 - 64 * v**58 + 24 * v**60 + 10 * v**64 + 24 * v**68 - 64 * v**70 + 45 * v**72,
             24 * v**40 - 34 * v**42 + 24 * v**44,
             8 * v**40 - 24 * v**42 + 40 * v**44 - 24 * v**46 + 8 * v**48,
             3 * v**60 - 27 * v**64 + 40 * v**66 - 27 * v**68 + 3 * v**72, 0,
             4 * v**40 - 8 * v**42 + 9 * v**44 - 8 * v**46 + 4 * v**48,
             v**40 - 4 * v**42 + 9 * v**44 - 14 * v**46 + 9 * v**48 - 4 * v**50 + v**52, -2 * v**22, 0,
             v**30 - 2 * v**34 + v**38, 2 * v**16, -v**28, -v**14, v**44 + 2 * v**46 + v**48,
             v**26, v**22, -2 * v**24, 0],
            [20 * v**68 - 64 * v**74 + 20 * v**80, 9 * v**44 - 18 * v**46 + 12 * v**48,
             3 * v**44 - 12 * v**46 + 18 * v**48 - 12 * v**50 + 6 * v**52,
             18 * v**70 - 36 * v**72 + 36 * v**74 - 2 * v**78, -5 * v**36,
             -4 * v**46 + v**48 - 8 * v**50 + v**52,
             -2 * v**46 + 5 * v**48 - 4 * v**50 + 3 * v**52 - 4 * v**54 + v**56, v**22 - 2 * v**24, 0, 0,
             0, 0, 0, 4 * v**50, -3 * v**28 + v**34, -3 * v**24 + v**26,
             -v**24 + 2 * v**26 - v**28 + v**30, v**28],
            [30 * v**56 + 30 * v**72, 3 * v**40 + 3 * v**44, v**40 + 4 * v**44 + v**48,
             -2 * v**60 + 18 * v**64 + 18 * v**68 - 2 * v**72,
             -v**24 + 4 * v**28 - 6 * v**32 + 4 * v**36 - v**40, v**40 - 4 * v**44 + v**48,
             -v**44 - v**48, v**20 + v**24, 0, 0, 0, 0, 0, -2 * v**44 - 2 * v**48, v**20 + v**32,
             v**20 + v**24, v**20 + v**28, -v**24 + 2 * v**26 - v**28],
            [0, 0, 0, -18 * v**74 + 30 * v**76 - 18 * v**78 + 6 * v**82, 4 * v**32 - 6 * v**36 - v**44,
             0, 0, 0, -v**20, v**38 + v**40, 0, 0, 0, 0, 0, 0, 0, v**30 - v**32],
            [-60 * v**72 + 60 * v**76 + 15 * v**80, 3 * v**48 - 12 * v**50 + 6 * v**52,
             v**48 - 4 * v**50 + 14 * v**52 - 8 * v**54 + 3 * v**56,
             9 * v**76 - 32 * v**78 + 18 * v**80 - 5 * v**84, 0, 10 * v**52 - 4 * v**54 + v**56,
             3 * v**52 - 8 * v**54 + 7 * v**56 - 2 * v**58 + v**60, v**24 - 2 * v**26 + v**28, 0,
             v**40 - v**44, 0, 0, 0, -4 * v**54 + 3 * v**56, -2 * v**30 + v**36,
             -2 * v**26 + v**28, -v**26 - v**30 + v**32, 0],
            [20 * v**52 - 10 * v**64 + 20 * v**76, 9 * v**40 - 24 * v**42 + 9 * v**44,
             3 * v**40 - 12 * v**42 + 30 * v**44 - 12 * v**46 + 3 * v**48,
             -18 * v**64 + 16 * v**66 - 18 * v**68, 0, -8 * v**42 + 6 * v**44 - 8 * v**46,
             -2 * v**42 + 9 * v**44 - 12 * v**46 + 9 * v**48 - 2 * v**50, v**20 + v**24, 0, 0, 0, 0, 0,
             -2 * v**46, -2 * v**26, -2 * v**22, -v**22 - v**26, 0],
            [60 * v**74 - 24 * v**78 + 64 * v**80 - 15 * v**82 - v**98,
             -6 * v**50 + 12 * v**52 - 12 * v**54,
             -2 * v**50 + 4 * v**52 - 14 * v**54 + 12 * v**56 - 6 * v**58, 0,
             -4 * v**34 + 6 * v**38 - 4 * v**42 + v**46, -8 * v**54 + 4 * v**56 - 4 * v**58,
             -v**54 + 6 * v**56 - 9 * v**58 + 4 * v**60 - 2 * v**62, 0, 0, 0, 0, 0, 0,
             4 * v**56 - 3 * v**58 - v**62, 0, 0, 0, -2 * v**32 + v**34],
            [-15 * v**56 - 64 * v**58 + 60 * v**60 - 10 * v**64 + 60 * v**68 - 64 * v**70 - 15 * v**72,
             18 * v**40 - 48 * v**42 + 18 * v**44,
             5 * v**40 - 32 * v**42 + 42 * v**44 - 32 * v**46 + 5 * v**48,
             4 * v**60 - 36 * v**64 + 64 * v**66 - 36 * v**68 + 4 * v**72,
             v**24 + 6 * v**32 + v**40, v**40 - 12 * v**42 + 18 * v**44 - 12 * v**46 + v**48,
             -6 * v**42 + 14 * v**44 - 20 * v**46 + 14 * v**48 - 6 * v**50, v**20 - 4 * v**22 + v**24, 0,
             0, 0, 0, 0, v**44 - 2 * v**46 + v**48, v**20 - 2 * v**26 + v**32,
             v**20 - 2 * v**22 + v**24, v**20 - v**22 - v**26 + v**28, v**24 + v**28],
            [10 * v**72 + 60 * v**76 - 64 * v**78 + 30 * v**80 + 20 * v**84 - 6 * v**88,
             11 * v**48 - 36 * v**50 + 21 * v**52,
             2 * v**48 - 16 * v**50 + 38 * v**52 - 28 * v**54 + 9 * v**56,
             -18 * v**76 + 32 * v**78 - 36 * v**80 + 6 * v**84, 0,
             -4 * v**50 + 10 * v**52 - 16 * v**54 + 4 * v**56,
             6 * v**52 - 16 * v**54 + 16 * v**56 - 8 * v**58 + 2 * v**60, 2 * v**26 - v**28, 0, 0, -v**16,
             -v**32, -v**16, 2 * v**54 + 2 * v**56 - 2 * v**58, 2 * v**30, 2 * v**26, v**26 + v**30, 0],
            [100 * v**72 - 60 * v**76 + 64 * v**78 - 20 * v**84 + 6 * v**88,
             -9 * v**48 + 36 * v**50 - 18 * v**52, -v**48 + 16 * v**50 - 36 * v**52 + 28 * v**54 - 7 * v**56,
             -9 * v**76 + 16 * v**78 + 4 * v**84, 0, 4 * v**50 - 14 * v**52 + 16 * v**54 - 3 * v**56,
             -8 * v**52 + 16 * v**54 - 18 * v**56 + 8 * v**58 - v**60, v**24 - 2 * v**26 + v**28, 0,
             v**40, 0, 0, 0, 4 * v**54 - 4 * v**56 + 2 * v**58, -2 * v**30 + v**36,
             -2 * v**26 + v**28, -v**26 - v**30 + v**32, 0],
            [30 * v**56 - 64 * v**58 + 24 * v**60 - 70 * v**64 + 24 * v**68 - 64 * v**70 + 30 * v**72,
             18 * v**40 - 18 * v**42 + 18 * v**44,
             7 * v**40 - 16 * v**42 + 18 * v**44 - 16 * v**46 + 7 * v**48,
             2 * v**60 - 9 * v**64 + 36 * v**66 - 9 * v**68 + 2 * v**72, 0,
             3 * v**40 - 4 * v**42 - v**44 - 4 * v**46 + 3 * v**48,
             v**40 - 4 * v**42 + v**44 - 2 * v**46 + v**48 - 4 * v**50 + v**52, -v**20 + 2 * v**22 - v**24,
             0, 2 * v**34, 0, 0, 0, -2 * v**44 + 2 * v**46 - 2 * v**48, -v**20 + 3 * v**26 - v**32,
             -v**20 + 3 * v**22 - v**24, -v**20 + v**22 - 2 * v**24 + v**26 - v**28, 0],
            [64 * v**62 + 10 * v**68 - 24 * v**72 + 64 * v**74 - 45 * v**76 + 6 * v**84,
             -18 * v**44 + 36 * v**46 - 24 * v**48,
             -5 * v**44 + 20 * v**46 - 36 * v**48 + 32 * v**50 - 8 * v**52,
             2 * v**66 + 26 * v**72 - 18 * v**74 + 2 * v**78, 0,
             -v**44 + 8 * v**46 - 10 * v**48 + 12 * v**50 - 5 * v**52,
             2 * v**46 - 7 * v**48 + 12 * v**50 - 16 * v**52 + 8 * v**54 - v**56,
             -v**22 + 2 * v**24 - 2 * v**26, 0, v**36 - v**38, 0, 0, 0,
             2 * v**50 - v**52 + 2 * v**54, -v**22 + 2 * v**28 - v**34, -v**22 + 2 * v**24 - v**26,
             -v**22 + v**24 + v**28 - v**30, 0],
            [-15 * v**56 - 90 * v**64 - 15 * v**72, 3 * v**40 - 18 * v**42 + 3 * v**44,
             -8 * v**42 + 22 * v**44 - 8 * v**46,
             -3 * v**60 + 27 * v**64 - 24 * v**66 + 27 * v**68 - 3 * v**72,
             0, -4 * v**42 + 7 * v**44 - 4 * v**46, 5 * v**44 - 14 * v**46 + 5 * v**48, 2 * v**22, 0,
             -v**30 + 2 * v**34 - v**38, 0, 0, 0, v**44 - 2 * v**46 + v**48, 3 * v**26, 3 * v**22,
             v**22 - 2 * v**24 + v**26, 0],
            [-20 * v**70 - 24 * v**74 + 64 * v**76 - 30 * v**78 + 6 * v**86,
             -12 * v**46 + 20 * v**48 - 18 * v**50,
             -4 * v**46 + 12 * v**48 - 18 * v**50 + 20 * v**52 - 8 * v**54, 0, -5 * v**34,
             4 * v**48 + 8 * v**52 - 4 * v**54,
             2 * v**48 + v**50 + 2 * v**52 - 7 * v**54 + 6 * v**56 - 2 * v**58, 0, 0, 0, 2 * v**18,
             -v**32, -v**16, -4 * v**52 + 2 * v**54 + 2 * v**56, 0, 0, 0, v**30],
            [-30 * v**56 + 64 * v**58 - 24 * v**60 - 100 * v**64 - 24 * v**68 + 64 * v**70 - 30 * v**72,
             -18 * v**40 + 16 * v**42 - 18 * v**44,
             -7 * v**40 + 16 * v**42 - 14 * v**44 + 16 * v**46 - 7 * v**48,
             4 * v**60 - 36 * v**64 + 64 * v**66 - 36 * v**68 + 4 * v**72,
             -v**24 + 4 * v**28 - 6 * v**32 + 4 * v**36 - v**40,
             -3 * v**40 + 4 * v**42 + 2 * v**44 + 4 * v**46 - 3 * v**48,
             -v**40 + 4 * v**42 - v**44 - v**48 + 4 * v**50 - v**52,
             v**20 - 4 * v**22 + v**24, 0, 0, -2 * v**16, v**28, v**14,
             2 * v**44 - 4 * v**46 + 2 * v**48, v**20 - 2 * v**26 + v**32, v**20 - 2 * v**22 + v**24,
             v**20 - v**22 - v**26 + v**28, -v**24 + 2 * v**26 - v**28],
            [81 * v**68, 0, 0, 18 * v**74 - 42 * v**76 + 18 * v**78 - 6 * v**82,
             v**28 - 4 * v**40 + v**44, 0, 0, 0, 0, -v**38 + v**40, 0, 0, 0, -3 * v**52, 0,
             0, 0, v**28 - v**30 + v**32],
            [15 * v**56 - 64 * v**58 + 84 * v**60 - 70 * v**64 + 84 * v**68 - 64 * v**70 + 15 * v**72,
             27 * v**40 - 54 * v**42 + 27 * v**44,
             9 * v**40 - 36 * v**42 + 54 * v**44 - 36 * v**46 + 9 * v**48,
             -v**60 + 9 * v**64 - 40 * v**66 + 9 * v**68 - v**72, 6 * v**32,
             3 * v**40 - 12 * v**42 + 27 * v**44 - 12 * v**46 + 3 * v**48,
             v**40 - 6 * v**42 + 18 * v**44 - 26 * v**46 + 18 * v**48 - 6 * v**50 + v**52,
             -v**20 + 2 * v**22 - v**24, 0, -v**30 + 2 * v**34 - v**38, 0, 0, 0,
             3 * v**44 - 6 * v**46 + 3 * v**48, -v**20 - v**26 - v**32, -v**20 - v**22 - v**24,
             -v**20 + 2 * v**24 - v**28, 0],
            [-81 * v**64, 0, 0, 27 * v**68 - 48 * v**70 + 27 * v**72 - 3 * v**76, 5 * v**32,
             0, 0, 0, 0, -2 * v**36 + v**40, 0, 0, 0, 3 * v**48, 0, 0, 0, -v**28],
            [-15 * v**56 + 64 * v**58 - 84 * v**60 + 70 * v**64 - 84 * v**68 + 64 * v**70 - 15 * v**72,
             -27 * v**40 + 54 * v**42 - 27 * v**44,
             -9 * v**40 + 36 * v**42 - 54 * v**44 + 36 * v**46 - 9 * v**48, v**60 + 4 * v**66 + v**72,
             v**24 - 4 * v**28 + 6 * v**32 - 4 * v**36 + v**40,
             -3 * v**40 + 12 * v**42 - 27 * v**44 + 12 * v**46 - 3 * v**48,
             -v**40 + 6 * v**42 - 18 * v**44 + 26 * v**46 - 18 * v**48 + 6 * v**50 - v**52,
             v**20 - 2 * v**22 + v**24, 0, -v**30 - v**38, 0, 0, 0,
             -3 * v**44 + 6 * v**46 - 3 * v**48, v**20 + v**26 + v**32, v**20 + v**22 + v**24,
             v**20 - 2 * v**24 + v**28, v**24 - 2 * v**26 + v**28],
            [15 * v**58 + 10 * v**66 - 60 * v**70 + 15 * v**74 - 20 * v**78,
             -10 * v**42 + 36 * v**44 - 12 * v**46,
             -2 * v**42 + 20 * v**44 - 38 * v**46 + 20 * v**48 - 4 * v**50, 0, 0,
             8 * v**44 - 12 * v**46 + 12 * v**48,
             2 * v**44 - 12 * v**46 + 18 * v**48 - 10 * v**50 + 4 * v**52, 0, v**18, 0,
             -v**14, -v**28, -v**14, -v**46 + 2 * v**48 - v**50, 0, 0, 0, 0],
            [60 * v**65 - 10 * v**69 + 84 * v**73 - 64 * v**75 - 6 * v**85,
             16 * v**45 - 48 * v**47 + 24 * v**49,
             4 * v**45 - 24 * v**47 + 44 * v**49 - 40 * v**51 + 8 * v**53, 0,
             -v**27 - 6 * v**35 + 4 * v**39 - v**43, -8 * v**47 + 20 * v**49 - 16 * v**51 + 4 * v**53,
             -2 * v**47 + 9 * v**49 - 20 * v**51 + 22 * v**53 - 10 * v**55 + v**57, 0, v**21, 0, v**15,
             v**30, v**15, -2 * v**51 + 4 * v**53 - 2 * v**55, 0, 0, 0, -v**27 + v**29 - v**31],
            [-60 * v**64 + 90 * v**68 - 60 * v**72, -6 * v**44 + 30 * v**46 - 9 * v**48,
             -v**44 + 12 * v**46 - 32 * v**48 + 20 * v**50 - 2 * v**52,
             -18 * v**70 + 44 * v**72 - 36 * v**74 + 2 * v**78, 0,
             4 * v**46 - 17 * v**48 + 8 * v**50 - v**52, -8 * v**48 + 20 * v**50 - 13 * v**52 + 4 * v**54,
             -v**22 + 2 * v**24, 0, 0, 0, 0, 0, 2 * v**50 - 4 * v**52, -v**28 - v**34, -v**24 - v**26,
             2 * v**26 - v**30, 0],
            [0, 0, 0, -3 * v**64 + 9 * v**68 - 48 * v**70 + 36 * v**72 - 3 * v**76, 0, 0, 0,
             0, -v**20, v**32 - v**36 + v**40, 0, 0, 0, 0, 0, 0, 0, 0],
            [-6 * v**110 + v**118, -2 * v**72 + 3 * v**74, -4 * v**76 + 2 * v**78,
             -4 * v**114, -4 * v**54 + v**58, -2 * v**76 + 2 * v**78, -4 * v**80 + v**82, 0,
             -v**30, -2 * v**58, -2 * v**26, -v**48, v**24, -2 * v**80 + v**82, -2 * v**44,
             2 * v**38, -2 * v**40 + v**42, -v**44 + v**46],
            [-20 * v**74 + 15 * v**82 - 6 * v**90, 3 * v**50 - 12 * v**52 + 7 * v**54,
             -4 * v**52 + 12 * v**54 - 12 * v**56 + 2 * v**58, -4 * v**78 - 8 * v**84,
             -4 * v**34 + 6 * v**38 - 4 * v**42 + v**46, -2 * v**52 + 6 * v**54 - 6 * v**56 + 2 * v**58,
             -10 * v**56 + 8 * v**58 - 4 * v**60, 0, 0, -2 * v**40, v**22, -v**36, v**18,
             -4 * v**56 + 3 * v**58 - 2 * v**60, -2 * v**28 + 2 * v**34, 2 * v**26 - 2 * v**28,
             v**26 - 2 * v**28 + 2 * v**30 - v**32, -2 * v**32 + v**34],
            [-30 * v**92 - v**108, -v**60 - 3 * v**64, -2 * v**64 - 2 * v**68, -8 * v**96,
             -6 * v**44 - v**52, 2 * v**64 - 2 * v**68, v**68 - v**72, 0, 0, 0, -v**20, v**40,
             -v**20, 2 * v**68 - v**72, 2 * v**36, -2 * v**32, -v**32 - v**36, -v**40],
            [-64 * v**86 + 15 * v**88 + 20 * v**92 - 6 * v**96 + v**104,
             3 * v**56 - 12 * v**58 + 11 * v**60, -4 * v**58 + 12 * v**60 - 12 * v**62 + 6 * v**64,
             -16 * v**90, -5 * v**40, 4 * v**60 - 8 * v**62 + 4 * v**64,
             -8 * v**62 + 6 * v**64 - 6 * v**66 + 2 * v**68, 0, v**24, 0, -v**24, v**40, -v**20,
             3 * v**64 - 2 * v**66 + v**68, -2 * v**34, 2 * v**30, v**30 + v**34, v**36],
            [15 * v**56 - 64 * v**58 + 70 * v**64 - 64 * v**70 + 15 * v**72,
             15 * v**40 - 28 * v**42 + 15 * v**44,
             4 * v**40 - 20 * v**42 + 28 * v**44 - 20 * v**46 + 4 * v**48, -32 * v**66,
             v**24 + v**40, 2 * v**40 - 8 * v**42 + 12 * v**44 - 8 * v**46 + 2 * v**48,
             -4 * v**42 + 9 * v**44 - 16 * v**46 + 9 * v**48 - 4 * v**50, 0, 0, 0, 2 * v**16, v**28,
             -v**14, 3 * v**44 - 2 * v**46 + 3 * v**48, 2 * v**26, -2 * v**22, -v**22 - v**26,
             v**24 + v**28],
            [60 * v**80 - 64 * v**82 - 15 * v**84 - 6 * v**92, 3 * v**52 - 16 * v**54 + 9 * v**56,
             -8 * v**54 + 10 * v**56 - 16 * v**58 + 4 * v**60, 8 * v**84, 0,
             6 * v**56 - 8 * v**58 + 2 * v**60, v**56 - 4 * v**58 + 8 * v**60 - 6 * v**62 + v**64, 0,
             -v**24, 0, 2 * v**20, v**36, -v**18, v**60 - 2 * v**62, -2 * v**32, 2 * v**28,
             v**28 + v**32, 0],
            [-10 * v**74 - 24 * v**78 + 64 * v**80 - 45 * v**82 - v**98, -6 * v**50 - 10 * v**54,
             -2 * v**50 + 4 * v**52 + 2 * v**54 + 4 * v**56 - 6 * v**58, 0, 6 * v**38 - 4 * v**42,
             4 * v**54 - 4 * v**58, -v**54 - 6 * v**56 + 5 * v**58 + 4 * v**60 - 2 * v**62, 0, 0, 0,
             -v**22, v**36, -v**18, -2 * v**56 + 3 * v**58 - v**62, 0, 0, 0, -v**32],
            [-60 * v**82 - 20 * v**90 + 6 * v**94, -2 * v**54 + 18 * v**56 - 9 * v**58,
             4 * v**56 - 18 * v**58 + 16 * v**60 - 4 * v**62, -8 * v**90, -5 * v**42,
             -8 * v**58 + 10 * v**60 - 2 * v**62, 10 * v**60 - 12 * v**62 + 6 * v**64 - v**66, 0, 0, 0,
             v**18, -v**36, v**18, -4 * v**62 + 2 * v**64, 2 * v**36, -2 * v**30,
             2 * v**32 - v**34, v**34],
            [-64 * v**58 + 84 * v**60 + 20 * v**64 + 84 * v**68 - 64 * v**70,
             21 * v**40 - 36 * v**42 + 21 * v**44,
             8 * v**40 - 28 * v**42 + 28 * v**44 - 28 * v**46 + 8 * v**48, -32 * v**66,
             v**24 - 4 * v**28 + 12 * v**32 - 4 * v**36 + v**40,
             2 * v**40 - 8 * v**42 + 12 * v**44 - 8 * v**46 + 2 * v**48,
             v**40 - 6 * v**42 + 10 * v**44 - 4 * v**46 + 10 * v**48 - 6 * v**50 + v**52, 0, 0, 0, 0, 0,
             0, 4 * v**46, 2 * v**26, -2 * v**22, -v**22 - v**26, v**24 - 2 * v**26 + v**28],
            [-70 * v**70 + 84 * v**74 - 64 * v**76 + 15 * v**78 + 20 * v**82 - 6 * v**86,
             15 * v**46 - 42 * v**48 + 24 * v**50,
             4 * v**46 - 20 * v**48 + 44 * v**50 - 32 * v**52 + 10 * v**54, -8 * v**72 - 12 * v**78,
             5 * v**34, -6 * v**48 + 18 * v**50 - 16 * v**52 + 4 * v**54,
             -2 * v**48 + 8 * v**50 - 22 * v**52 + 19 * v**54 - 8 * v**56 + 2 * v**58, 0, 0, 2 * v**40, 0, 0,
             0, -6 * v**52 + 3 * v**54 - 2 * v**56, 2 * v**26, -2 * v**24, -v**24 + 2 * v**26, -v**30],
            [-90 * v**74 - 24 * v**78 + 64 * v**80 - 45 * v**82 + 6 * v**90 - v**98,
             -9 * v**50 + 18 * v**52 - 18 * v**54,
             -2 * v**50 + 8 * v**52 - 18 * v**54 + 20 * v**56 - 8 * v**58,
             -8 * v**78, -4 * v**34 + v**46, 2 * v**52 - 4 * v**54 + 8 * v**56 - 6 * v**58,
             -v**54 + 6 * v**56 - 8 * v**58 + 8 * v**60 - 2 * v**62, 0, 0, 0, 0, 0, 0,
             -2 * v**56 - v**58 + 2 * v**60 - v**62, 2 * v**28, -2 * v**26, -v**26 + 2 * v**28,
             -v**32 + v**34],
            [-15 * v**56 + 60 * v**60 + 60 * v**68 - 15 * v**72, 9 * v**40 - 36 * v**42 + 9 * v**44,
             2 * v**40 - 20 * v**42 + 36 * v**44 - 20 * v**46 + 2 * v**48, -16 * v**66,
             v**24 - 4 * v**28 - 4 * v**36 + v**40, -8 * v**42 + 16 * v**44 - 8 * v**46,
             -2 * v**42 + 13 * v**44 - 16 * v**46 + 13 * v**48 - 2 * v**50, 0, 0, 0, 0, 0, 0,
             v**44 + v**48, -2 * v**26, 2 * v**22, v**22 + v**26, v**24 - 2 * v**26 + v**28],
            [-81 * v**68, 0, 0, -24 * v**76, -v**28 + 4 * v**32 - 6 * v**36 + 4 * v**40 - 2 * v**44, 0,
             0, 0, -v**20, 0, 0, 0, 0, 3 * v**52, 0, 0, 0, -v**28 + 2 * v**30 - 2 * v**32],
            [90 * v**70 - 60 * v**74 + 15 * v**78 - 20 * v**82, -3 * v**46 + 22 * v**48 - 6 * v**50,
             8 * v**48 - 26 * v**50 + 12 * v**52 - 2 * v**54, -8 * v**72 + 12 * v**78, 0,
             2 * v**48 - 10 * v**50 + 8 * v**52, -5 * v**50 + 12 * v**52 - 12 * v**54 + 2 * v**56, 0, 0,
             2 * v**40, -2 * v**18, -v**32, v**16, 2 * v**52 - v**54, 2 * v**26, -2 * v**24,
             -v**24 + 2 * v**26, 0],
            [-80 * v**74 + 24 * v**78 - 64 * v**80 + 30 * v**82 - 6 * v**90 + v**98,
             9 * v**50 - 24 * v**52 + 19 * v**54, 2 * v**50 - 8 * v**52 + 26 * v**54 - 24 * v**56 + 8 * v**58,
             -4 * v**78 + 8 * v**84, 0, -2 * v**52 + 6 * v**54 - 10 * v**56 + 6 * v**58,
             v**54 - 8 * v**56 + 13 * v**58 - 8 * v**60 + 2 * v**62, 0, 0, 2 * v**40, v**22, -v**36,
             v**18, 2 * v**58 - 2 * v**60 + v**62, -2 * v**28 - 2 * v**34, 2 * v**26 + 2 * v**28,
             v**26 - 2 * v**28 - 2 * v**30 + v**32, 0],
            [-15 * v**58 - 24 * v**62 + 10 * v**66 - 60 * v**70 + 64 * v**72 - 15 * v**74 - 20 * v**78,
             -18 * v**42 + 42 * v**44 - 21 * v**46,
             -4 * v**42 + 28 * v**44 - 46 * v**46 + 24 * v**48 - 8 * v**50, -16 * v**72, 0,
             -2 * v**42 + 8 * v**44 - 18 * v**46 + 14 * v**48 - 2 * v**50,
             4 * v**44 - 14 * v**46 + 24 * v**48 - 14 * v**50 + 4 * v**52 - v**54, 0, v**18, 0, 0, 0,
             0, -3 * v**46 + 2 * v**48 - 3 * v**50, -2 * v**30, 2 * v**24, -2 * v**26 + v**28, 0],
            [-64 * v**62 + 24 * v**64 - 10 * v**68 + 84 * v**72 - 128 * v**74 + 45 * v**76 - 6 * v**84,
             24 * v**44 - 48 * v**46 + 32 * v**48,
             6 * v**44 - 32 * v**46 + 44 * v**48 - 40 * v**50 + 12 * v**52, 24 * v**72, 0,
             2 * v**44 - 8 * v**46 + 16 * v**48 - 16 * v**50 + 6 * v**52,
             -4 * v**46 + 11 * v**48 - 16 * v**50 + 17 * v**52 - 10 * v**54 + 2 * v**56, 0, 0, 0, -v**20,
             v**32, -v**16, -2 * v**50 + v**52 - 2 * v**54, 0, 0, 0, 0],
            [30 * v**56 - 64 * v**58 + 84 * v**60 - 90 * v**64 + 84 * v**68 - 64 * v**70 + 30 * v**72,
             33 * v**40 - 68 * v**42 + 33 * v**44,
             10 * v**40 - 44 * v**42 + 72 * v**44 - 44 * v**46 + 10 * v**48, -16 * v**66, 0,
             4 * v**40 - 16 * v**42 + 24 * v**44 - 16 * v**46 + 4 * v**48,
             v**40 - 6 * v**42 + 22 * v**44 - 28 * v**46 + 22 * v**48 - 6 * v**50 + v**52, 0, 0, 0,
             -2 * v**16, -v**28, v**14, 2 * v**44 - 2 * v**46 + 2 * v**48, -2 * v**26, 2 * v**22,
             v**22 + v**26, 0],
            [-81 * v**74, 0, 0, 12 * v**74, 5 * v**38, 0, 0, 0, v**22, -2 * v**38,
             0, 0, 0, 3 * v**54, 0, 0, 0, -v**30],
            [60 * v**64 - 70 * v**68 + 60 * v**72 - 64 * v**74 + 20 * v**80,
             15 * v**44 - 48 * v**46 + 21 * v**48,
             4 * v**44 - 24 * v**46 + 50 * v**48 - 32 * v**50 + 8 * v**52,
             16 * v**72, -5 * v**36, -8 * v**46 + 22 * v**48 - 16 * v**50 + 2 * v**52,
             -2 * v**46 + 13 * v**48 - 24 * v**50 + 20 * v**52 - 8 * v**54 + v**56, 0, 0, 0, 0, 0, 0,
             -6 * v**50 + 4 * v**52, 2 * v**28, -2 * v**24, -v**24 - v**28, v**28],
            [45 * v**56 - 36 * v**60 + 110 * v**64 - 36 * v**68 + 45 * v**72, 32 * v**42,
             2 * v**40 + 16 * v**42 - 28 * v**44 + 16 * v**46 + 2 * v**48, 0, -4 * v**28 - 4 * v**36,
             2 * v**40 + 8 * v**42 - 20 * v**44 + 8 * v**46 + 2 * v**48,
             v**40 + 2 * v**42 - 13 * v**44 + 20 * v**46 - 13 * v**48 + 2 * v**50 + v**52, 0, 0, 0,
             2 * v**16, v**28, -v**14, -3 * v**44 + 6 * v**46 - 3 * v**48, 0, 0, 0, -2 * v**26],
            [-60 * v**65 + 10 * v**69 - 84 * v**73 + 64 * v**75 + 6 * v**85,
             -16 * v**45 + 48 * v**47 - 24 * v**49,
             -4 * v**45 + 24 * v**47 - 44 * v**49 + 40 * v**51 - 8 * v**53, 0,
             v**27 + 6 * v**35 - 4 * v**39 + v**43, 8 * v**47 - 20 * v**49 + 16 * v**51 - 4 * v**53,
             2 * v**47 - 9 * v**49 + 20 * v**51 - 22 * v**53 + 10 * v**55 - v**57, 0, -v**21, 0, -v**15,
             v**30, -v**15, 2 * v**51 - 4 * v**53 + 2 * v**55, 0, 0, 0, v**27 - v**29 + v**31],
            [64 * v**60 - 24 * v**62 + 40 * v**66 - 24 * v**70 + 64 * v**72 - 45 * v**74,
             -21 * v**42 + 30 * v**44 - 24 * v**46,
             -8 * v**42 + 20 * v**44 - 32 * v**46 + 24 * v**48 - 10 * v**50, -4 * v**66, 0,
             -2 * v**42 + 6 * v**44 - 8 * v**46 + 8 * v**48 - 4 * v**50,
             -v**42 + 2 * v**44 - 8 * v**46 + 8 * v**48 - 8 * v**50 + 6 * v**52 - 2 * v**54, 0, 0, 2 * v**34,
             0, 0, 0, -v**50, -2 * v**24, 2 * v**22, v**22 - 2 * v**24, 0],
            [81 * v**70, 0, 0, -12 * v**74, -v**26 + 4 * v**30 - 6 * v**34 + 8 * v**38 - v**42, 0, 0, 0,
             0, -2 * v**38, 0, 0, 0, -3 * v**50, 0, 0, 0, -v**26 + 3 * v**28 - v**30],
            [-30 * v**58 - 24 * v**62 + 64 * v**72 - 30 * v**74, -8 * v**42 + 6 * v**44 - 9 * v**46,
             -2 * v**42 + 8 * v**44 - 8 * v**46 + 4 * v**48 - 4 * v**50, 16 * v**72, 0,
             -2 * v**42 + 2 * v**46 + 2 * v**48 - 2 * v**50, 2 * v**44 - 2 * v**46 - 2 * v**48 - v**54, 0, 0,
             0, v**14, -v**28, v**14, 2 * v**46 + 2 * v**50, 2 * v**30, -2 * v**24,
             2 * v**26 - v**28, 0]]
    if typ[0] == 'H' and n == 3:
        v = paramL[0]
        ir5 = ir(5)
        cc = [i - 1 for i in [6, 8, 9, 10]]
        ch = [i - 1 for i in [1, 3, 5, 6, 9]]
        t1 = [[-1, -1, -1, -1], [0, v**4, 0, -5 * v**12], [(1 - ir5) * v**2, 0, ir5 * v**6, 3 * v**10],
            [ir5 * v**2, 0, (1 - ir5) * v**6, 3 * v**10], [v**3, -v**5, v**9, -4 * v**15]]
    if typ[0] == 'H' and n == 4:
        v = paramL[0]
        ir5 = ir(5)
        cc = [i - 1 for i in [19, 21, 25, 27, 31]]
        ch = [i - 1 for i in [1, 3, 5, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 20, 22, 23,
                          24, 25, 26, 27, 29, 30, 31, 33, 34]]
        t1 = [[v**28, v**32, v**44, v**52, v**76],
            [(1 - ir5) * v**20 + ir5 * v**22, -2 * v**22 + ir5 * v**26, -2 * v**32 + v**34,
             -ir5 * v**38 + (ir5 - 1) * v**40, -2 * v**56 + (1 - ir5) * v**58],
            [ir5 * v**20 + (1 - ir5) * v**22, -2 * v**22 + (1 - ir5) * v**26, -2 * v**32 + v**34,
             (ir5 - 1) * v**38 - ir5 * v**40, -2 * v**56 + ir5 * v**58],
            [v**12 - v**14 + v**16, v**12 + (-2 * ir5) * v**16 + v**20, v**20 - 2 * v**22 + v**24,
             v**24 - v**26 + v**28, v**36 + (-2 + 2 * ir5) * v**38 + v**40],
            [v**12 - v**14 + v**16, v**12 + (-2 + 2 * ir5) * v**16 + v**20, v**20 - 2 * v**22 + v**24,
             v**24 - v**26 + v**28, v**36 + (-2 * ir5) * v**38 + v**40],
            [-2 * v**14, -2 * v**16, 2 * v**20 - 2 * v**22 + 2 * v**24, -2 * v**26, -2 * v**38],
            [-3 * v**14, 2 * v**16, v**20 - 4 * v**22 + v**24, 3 * v**26, 2 * v**38],
            [(-1 - ir5) * v**18 + ir5 * v**20, (2 - 2 * ir5) * v**20 + ir5 * v**24, 0,
             (-2 + ir5) * v**34 + (1 - ir5) * v**36, (+2 * ir5) * v**50 + (1 - ir5) * v**52],
            [(-2 + ir5) * v**18 + (1 - ir5) * v**20, (+2 * ir5) * v**20 + (1 - ir5) * v**24, 0,
             (-1 - ir5) * v**34 + ir5 * v**36, (2 - 2 * ir5) * v**50 + ir5 * v**52],
            [v**12 - 2 * v**14 + v**16, v**12 - 2 * v**16 + v**20, v**20 - 4 * v**22 + v**24,
             v**24 - 2 * v**26 + v**28, v**36 - 2 * v**38 + v**40],
            [ir5 * v**12 + (-1 - 2 * ir5) * v**14 + ir5 * v**16, ir5 * v**12 - 2 * v**16 + ir5 * v**20,
             v**20 + v**24, (ir5 - 1) * v**24 + (3 - 2 * ir5) * v**26 + (ir5 - 1) * v**28,
             (1 - ir5) * v**36 - 2 * v**38 + (1 - ir5) * v**40],
            [(1 - ir5) * v**12 + (-3 + 2 * ir5) * v**14 + (1 - ir5) * v**16,
             (1 - ir5) * v**12 - 2 * v**16 + (1 - ir5) * v**20, v**20 + v**24,
             -ir5 * v**24 + (1 + 2 * ir5) * v**26 - ir5 * v**28, ir5 * v**36 - 2 * v**38 + ir5 * v**40],
            [-2 * v**17 + v**19, -2 * v**19 + v**23, -v**25 + 2 * v**27 - 2 * v**29, 2 * v**32 - v**34,
             -2 * v**47 + v**49],
            [2 * v**17 - v**19, 2 * v**19 - v**23, v**25 - 2 * v**27 + 2 * v**29, 2 * v**32 - v**34,
             2 * v**47 - v**49],
            [v**12 + v**14 + v**16, v**12 - 4 * v**16 + v**20, 0, v**24 + v**26 + v**28,
             v**36 - 4 * v**38 + v**40],
            [ir5 * v**12 + (1 - 2 * ir5) * v**14 + ir5 * v**16,
             ir5 * v**12 + (2 - 4 * ir5) * v**16 + ir5 * v**20, 2 * v**20 - 4 * v**22 + 2 * v**24,
             (ir5 - 1) * v**24 + (1 - 2 * ir5) * v**26 + (ir5 - 1) * v**28,
             (1 - ir5) * v**36 + (-2 + 4 * ir5) * v**38 + (1 - ir5) * v**40],
            [(1 - ir5) * v**12 + (-1 + 2 * ir5) * v**14 + (1 - ir5) * v**16,
             (1 - ir5) * v**12 + (-2 + 4 * ir5) * v**16 + (1 - ir5) * v**20,
             2 * v**20 - 4 * v**22 + 2 * v**24, -ir5 * v**24 + (-1 + 2 * ir5) * v**26 - ir5 * v**28,
             ir5 * v**36 + (2 - 4 * ir5) * v**38 + ir5 * v**40],
            [(ir5 - 1) * v**12 + (1 - 2 * ir5) * v**14 + (ir5 - 1) * v**16,
             (ir5 - 1) * v**12 + (ir5 - 1) * v**20, v**20 - 2 * v**22 + v**24,
             -ir5 * v**24 + (-1 + 2 * ir5) * v**26 - ir5 * v**28, -ir5 * v**36 - ir5 * v**40],
            [-ir5 * v**12 + (-1 + 2 * ir5) * v**14 - ir5 * v**16, -ir5 * v**12 - ir5 * v**20,
             v**20 - 2 * v**22 + v**24, (ir5 - 1) * v**24 + (1 - 2 * ir5) * v**26 + (ir5 - 1) * v**28,
             (ir5 - 1) * v**36 + (ir5 - 1) * v**40],
            [0, 0, -v**24 + 4 * v**26 - 2 * v**28, 0, 0],
            [ir5 * v**12 + (-2 * ir5) * v**14 + ir5 * v**16,
             ir5 * v**12 + (-2 * ir5) * v**16 + ir5 * v**20, -v**20 + 2 * v**22 - v**24,
             (1 - ir5) * v**24 + (-2 + 2 * ir5) * v**26 + (1 - ir5) * v**28,
             (1 - ir5) * v**36 + (-2 + 2 * ir5) * v**38 + (1 - ir5) * v**40],
            [(1 - ir5) * v**12 + (-2 + 2 * ir5) * v**14 + (1 - ir5) * v**16,
             (1 - ir5) * v**12 + (-2 + 2 * ir5) * v**16 + (1 - ir5) * v**20, -v**20 + 2 * v**22 - v**24,
             ir5 * v**24 + (-2 * ir5) * v**26 + ir5 * v**28,
             ir5 * v**36 + (-2 * ir5) * v**38 + ir5 * v**40],
            [-v**14 + 2 * v**16 - 2 * v**18, -v**14 + 2 * v**18 - 2 * v**22, 0,
             v**28 - 2 * v**30 + 2 * v**32, -v**42 + 2 * v**44 - 2 * v**46],
            [-v**12 + 2 * v**14 - v**16, -v**12 + 2 * v**16 - v**20, -2 * v**22,
             -v**24 + 2 * v**26 - v**28, -v**36 + 2 * v**38 - v**40],
            [v**12 + v**16, v**12 + v**20, -2 * v**20 + 4 * v**22 - 2 * v**24, -v**24 - v**28,
             v**36 + v**40]]
    if typ[0] == 'I':
        m = int(typ[1:])
        if m == 5:
            v = paramL[0]
            ir5 = ir(5)
            cc = [3]
            ch = [0, 1, 2, 3]
            t1 = [[v**8], [1], [-ir5 * v**4], [(ir5 - 1) * v**4]]
        else:
            c = conjclassdata(typ, n)['reps']
            cc = range(len(c))
            ch = range(len(c))
            z = rootof1(m)
            if m % 2 == 0:
                t1 = [[paramL[0]**(2 * i.count(0)) * paramL[1]**(2 * i.count(1)) for i in c],
                    [(-1)**i.count(1) * paramL[0]**(2 * i.count(0)) for i in c],
                    [(-1)**i.count(0) * paramL[1]**(2 * i.count(1)) for i in c],
                    [(-1)**len(i) for i in c]]
                for j in range(1, (m - 2) // 2 + 1):
                    chi = [2, paramL[0]**2 - 1, paramL[1]**2 - 1]
                    chi.extend([(paramL[0] * paramL[1])**(len(i) // 2) * (z**(j * len(i) // 2) +
                                                  z**(-j * len(i) // 2)) for i in c[3:]])
                    t1.append(chi)
            else:
                t1 = [[paramL[0]**(2 * len(i))
                       for i in c], [(-1)**len(i) for i in c]]
                for j in range(1, (m - 1) // 2 + 1):
                    chi = [2, paramL[0]**2 - 1]
                    chi.extend([paramL[0]**len(i) * (z**(j * len(i) // 2) +
                                   z**(-j * len(i) // 2)) for i in c[2:]])
                    t1.append(chi)
    return [cc, ch, t1]

# F heckechartable


def heckechartable(W, paramL=1):
    """returns  the character table of the Iwahori-Hecke algebra of W.
    Here,  'paramL'  is a  list of elements in a base ring, one for
    each simple reflection in W, such that two parameters are equal
    whenever the corresponding reflections are conjugate in W.  For
    example, a typical parameter  list is given by  [u^a, u^b, ...]
    where [a, b, ...] are a list of weights as in 'ainvariants'.

    It is allowed that  paramL  is just one element,  in which case
    all parameters  will be set equal to that element.  The default
    value  is 1,  in which case  the function returns the  ordinary
    character table of W.

    The Iwahori-Hecke algebra of W is an  associative algebra  with
    a basis {T_w | w in W}. The multiplication is given as follows:

     T_s*T_w=T_{sw}   if l(sw)=l(w)+1

     T_s*T_w=T_{sw}+(paramL[s]-paramL[s]^(-1)) T_w if l(sw)=l(w)-1

    where s is a simple reflection and  w in W.  If v=1,  then this
    algebra is  just the  group algebra of W.  Otherwise,  assuming
    that v is  not a root of unity,  the algebra is  semisimple and
    abstractly isomorphic to the  group algebra of W. Its character
    table is a v-deformation of the ordinary character  table of W.
    The  function returns the square matrix of character values  on
    the elements {v(w) T_w}  where  w runs over  a complete  set of
    representatives of minimal length in the conjugacy classes of W
    (as returned by 'conjugacyclasses(W)')  and v(w) is the product
    of the parameter values  paramL[s] where  s runs over a reduced
    expression of w.  If all parameters are  specialised to 1, then
    the resulting matrix  is the ordinary character  table of W (as
    returned by 'chartable(W)').

    >>> heckechartable(coxeter("B", 2), [v**3, v**2])
    {'coxeter': coxeter('B',2),
     'irreducibles': [[1, v**4, v**8, -1, -v**4],
      [2, -1+v**4, -2*v**10, -1+v**6, 0],
      [1, -1, 1, -1, 1],
      [1, v**4, v**20, v**6, v**10],
      [1, -1, v**12, v**6, -v**6]],
     'params': [v**3, v**2]}

    See also 'classpolynomials', 'heckecharvalues', 'schurelms' and
    'displaychartable'.
    """
    if isinstance(paramL, list):
        vs = paramL[:]
    else:
        vs = len(W.rank) * [paramL]
    ti = chartable(W)
    if all(x == x**0 for x in vs):
        return ti
    nti = {'params': vs, 'coxeter': W}
    ct = W.cartantype[0]
    if len(W.cartantype) > 1:   # can use induction
        nti['irreducibles'] = heckechartable(coxeter(ct[0], len(ct[1])),
                    [vs[s] for s in ct[1]])['irreducibles']
        for t in W.cartantype[1:]:
            nt = heckechartable(coxeter(t[0], len(t[1])), [vs[s] for s in t[1]])
            nti['irreducibles'] = kroneckerproduct(nti['irreducibles'],
                                                  nt['irreducibles'])
    else:   # now build table from heckeirrdata
        cc, ch, matv = heckeirrdata(ct[0], len(ct[1]), [vs[s] for s in ct[1]])
        cl = conjugacyclasses(W)['reps']
        lc = [len(c) for c in cl]
        cind = []
        for w in cl:
            x = 1
            for i in w:
                x *= vs[i]
            cind.append(x)
        if 0 < len(ch) < len(cl):     # add dual characters
            ivs = []
            for s in ct[1]:
                if vs[s] == 1 or vs[s] == -1:
                    ivs.append(vs[s])
                else:
                    ivs.append(vs[s]**(-1))
            tt1 = heckeirrdata(ct[0], len(ct[1]), ivs)[2]
            # tt1=heckeirrdata(ct[0], len(ct[1]), [1//vs[s] for s in ct[1]])[2]
            nch = ch[:]
            for i in range(len(ch)):
                i1 = ti['permsgn'][ch[i]]
                if i1 > ch[i]:
                    matv.append([(-1)**lc[cc[j]] * cind[cc[j]]**2 * tt1[i][j]
                                 for j in range(len(cc))])
                    nch.append(i1)
            matv = [matv[nch.index(i)] for i in range(len(nch))]
        if len(cc) == len(cl):
            nti['irreducibles'] = matv
        else:
            tr = transposemat(matv)
            onegood = [c for c in range(len(cl))
                       if set(cl[c]) == set(W.rank) and
                       c not in cc]
            if onegood:      # add 1-good classes
                for c in onegood:
                    xv = []
                    for x in ti['irreducibles']:
                        if x[c] == 0:
                            xv.append(0)
                        else:
                            xv.append(x[c] * cind[c] *
                                     vs[ct[1][0]]**((len(cl[c]) * x[lc.index(1)]) // x[0]))
                    tr.append(xv[:])
                    cc.append(c)
            s = len(W.rank)
            while len(cc) < len(cl):     # add non-cuspidal classes
                s -= 1
                J = list(W.rank)
                J.remove(s)
                W1 = reflectionsubgroup(W, J)
                fus = fusionconjugacyclasses(W1, W)
                ind = inductiontable(W1, W)['scalar']
                nti1 = heckechartable(W1, [vs[u] for u in J])['irreducibles']
                for c in fus:
                    if c not in cc:
                        tr.append([sum(i[j] * nti1[j][fus.index(c)]
                                      for j in range(len(nti1))) for i in ind])
                        cc.append(c)
            nti['irreducibles'] = transposemat([tr[cc.index(i)]
                                                for i in range(len(cc))])
    return nti

# F heckecharvalues


def heckecharvalues(W, paramL, lw, clpols=[]):
    """returns  the  character values of a generic Iwahori-Hecke algebra
    on all basis elements  T_w  where  w runs  over a given list. The
    algebra is defined  with respect to  the parameters  specified by
    the argument paramL; see also 'heckechartable'. For w in W and an
    irreducible character chi, we have

       chi(v(w) T_w) = sum_C  f_{w, C} chi(T_C)

    where  f_{w, C}  are the class polynomials  and  chi(T_C) are  the
    entries  of the character table of the Iwahori-Hecke algebra. The
    argument  lw  contains the list of  elements,  given  as  reduced
    expressions, for which the character values are to be computed.

    >>> W = coxeter("B", 2)
    >>> a = allwords(W); a
    [[], [0], [1], [0, 1], [1, 0], [0, 1, 0], [1, 0, 1], [0, 1, 0, 1]]
    >>> heckecharvalues(W, [v**3, v**2], a)
    [[1, 2, 1, 1, 1],
     [-1, -1+v**6, -1, v**6, v**6],
     [v**4, -1+v**4, -1, v**4, -1],
     [-v**4, 0, 1, v**10, -v**6],
     [-v**4, 0, 1, v**10, -v**6],
     [v**4, -v**6+v**10, -1, v**16, -v**12],
     [-v**8, -v**4+v**10, -1, v**14, v**6],
     [v**8, -2*v**10, 1, v**20, v**12]]

    See also 'heckechartable' and 'classpolynomials'.
    """
    if isinstance(paramL, list):
        vs = paramL[:]
    else:
        vs = len(W.rank) * [paramL]
    ti = heckechartable(W, vs)['irreducibles']
    maxl = max(len(w) for w in lw)
    # elms=allwords(W, maxl)
    if clpols == []:
        cpmat = allclasspolynomials(W, [p**2 for p in vs], maxl)
    else:
        cpmat = clpols
    lc = []
    for w in lw:
        # cp=cpmat[elms.index(w)]
        cp = cpmat[W.wordtocoxelm(w)]
        lc.append([sum(cp[j] * irr[j] for j in range(len(ti))) for irr in ti])
    return lc

# F heckecentraltable


def heckecentraltable(W, paramL):
    """returns the matrix of central character values on the standard basis of
    the  centre of a generic Iwahori-Hecke algebra. This matrix is uniquely
    determined  by the condition that its product with the transpose of the
    character table of  the algebra  is the  diagonal matrix  with diagonal
    entries given by the Schur elements.

    (The current  implementation  uses class polynomials  and,  hence, will
    only work for W  of order at most around 50000.  I intend to add a more
    efficient version, which will also be meant to work  for W of type E_8,
    in a later version.)

    >>> W = coxeter("B", 2)
    >>> v = lpol([1], 1, 'v')
    >>> ti = heckechartable(W, [v**2, v])
    >>> ct = heckecentraltable(W, [v**2, v]); ct
    [[1, v**(-4)+1, v**(-8), -v**(-4)-v**(-2), -v**(-8)-v**(-2)],
     [1, -v**(-2)+1, -v**(-6), -v**(-4)+1, v**(-6)-v**(-4)-v**(-2)+1],
     [1, -v**(-6)-v**(-2), v**(-12), -v**(-6)-v**(-4), v**(-10)+v**(-8)],
     [1, 1+v**4, 1, 1+v**2, v**2+v**4],
     [1, -v**(-2)-v**2, v**(-4), v**(-2)+1, -v**(-4)-v**2]]
    >>> matmult(ti['irreducibles'], transposemat(ct))
    [[v**(-6)+2*v**(-4)+2*v**(-2)+2+v**2, 0, 0, 0, 0],
     [0, v**(-4)+v**(-2)+v**2+v**4, 0, 0, 0],
     [0, 0, v**(-12)+v**(-10)+v**(-8)+2*v**(-6)+v**(-4)+v**(-2)+1, 0, 0],
     [0, 0, 0, 1+v**2+v**4+2*v**6+v**8+v**10+v**12, 0],
     [0, 0, 0, 0, v**(-2)+2+2*v**2+2*v**4+v**6]]
    """
    if isinstance(paramL, list):
        vs = paramL[:]
    else:
        vs = len(W.rank) * [paramL]
    indw = []
    aw = allwords(W)
    ivs = []
    for s in W.rank:
        if vs[s] == 1 or vs[s] == -1:
            ivs.append(vs[s])
        else:
            ivs.append(vs[s]**(-1))
    for w in aw:
        cind = 1
        for i in w:
            cind *= ivs[i]
        indw.append(cind)
    cpmat = allclasspolynomials(W, [p**2 for p in vs])
    cpmat = [cpmat[W.wordtocoxelm(w)] for w in aw]
    cpmat = [[indw[i] * cpmat[i][j] for j in range(len(cpmat[0]))]
             for i in range(len(cpmat))]
    cpmat = matmult(heckechartable(W, vs)['irreducibles'],
                    matmult(transposemat(cpmat), cpmat))
    x1 = [chi[0] for chi in chartable(W)['irreducibles']]
    return [[divmod(z, x1[i])[0] for z in cpmat[i]]
            for i in range(len(cpmat[0]))]

# F schurelmA


def schurelmA(alpha, u):
    """returns the Schur element corresponding to the partition alpha.
    (Taken from the gap-chevie library.)
    """
    l = len(alpha)
    lbd = [i + alpha[::-1][i] for i in range(l)]
    if u == 1 or u == -1:
        u1 = u
    else:
        u1 = u**(-1)
    res = u**((l * (l - 1) * (l - 2)) // 6)
    for i in lbd:
        for j in range(i):
            if j in lbd:
                res *= u1**j
            else:
                res *= sum(u**e for e in range(i - j))
    return res

# F schurelmB


def schurelmB(bip, v, u):
    """returns the Schur element corresponding to the bipartition bip.
    (Taken from the gap-chevie library.)
    """
    if u == 1 or u == -1:
        u1 = u
    else:
        u1 = u**(-1)
    if v == 1 or v == -1:
        v1 = v
    else:
        v1 = v**(-1)
    la, mu = redlusztigsymbolB(1, 1, bip)
    m = len(mu)
    if m == 0:
        res = 1
    elif m == 1:
        res = u1 * (u + v)
    else:
        res = u**(((2 * m + 1) * m * (m - 2)) // 3) * v**((m * (m - 1)) // 2) * (u + v)**m
    for i in la:
        for j in range(i):
            if j in la:
                if j in mu:
                    res *= u1**(2 * j)
                else:
                    if i - 2 * j >= 1:
                        res *= u**(i - 2 * j - 1) * v + (u1**j)
                    else:
                        res *= (u1**(2 * j + 1 - i)) * v + (u1**j)
            else:
                if j in mu:
                    res *= sum(u**e for e in range(i - j)) * (u1**j)
                else:
                    res *= sum(u**e for e in range(i - j)) * (u**(i - j - 1) * v + 1)
    for i in mu:
        for j in range(i):
            if j in mu:
                if j in la:
                    if j == 0:
                        res *= u * v1
                    else:
                        res *= u1**(2 * j - 1) * v1
                else:
                    if i - 2 * j + 1 >= 0:
                        res *= u**(i - 2 * j + 1) * v1 + u1**j
                    else:
                        res *= (u1**(2 * j - 1 - i)) * v1 + u1**j
            else:
                if j in la:
                    if j == 0:
                        res *= sum(u**e for e in range(i)) * u * v1
                    else:
                        res *= sum(u**e for e in range(i - j)) * (u1**(j - 1)) * v1
                else:
                    res *= sum(u**e for e in range(i - j)) * (u**(i - j + 1) * v1 + 1)
        if i in la:
            if i == 0:
                res = divmod(res, u1 * v + 1)[0]
            else:
                res = divmod(res, u**(i - 1) * v + u**i)[0]
    return res

# F schurelmdata


def schurelmdata(typ, n, vs):
    """returns  the Schur elements of the Iwahori-Hecke algebra of a
    given type and rank with respect to a list of parameters. The
    data are taken from the corresponding files in  gap-chevie.
    """
    if typ[0] == 'A':
        return [schurelmA(alpha, vs[0]) for alpha in partitions(n + 1)]
    if typ[0] == 'B' and n == 2:
        return [schurelmB(mu, vs[1], vs[0]) for mu in partitiontuples(2, 2)]
    if typ[0] == 'C' and n == 2:
        return [schurelmB(mu, vs[0], vs[1]) for mu in partitiontuples(2, 2)]
    if (typ[0] == 'B' or typ[0] == 'C') and n >= 3:
        return [schurelmB(mu, vs[0], vs[1]) for mu in partitiontuples(n, 2)]
    if typ[0] == 'D':
        vcyc = []
        for mu in partitiontuples(n, 2):
            s = schurelmB(mu, vs[0]**0, vs[0])
            if mu[0] == mu[1]:
                vcyc.append(s)
                vcyc.append(s)
            elif mu[0] < mu[1]:
                vcyc.append(divmod(s, 2)[0])
        return vcyc
    if typ[0] == 'G':
        u, v, squv = vs[0], vs[1], vs[2]
        if u == 1 or u == -1:
            u1 = u
        else:
            u1 = u**(-1)
        if v == 1 or v == -1:
            v1 = v
        else:
            v1 = v**(-1)
        return [(1 + u) * (v + 1) * (u * v - squv + 1) * (u * v + squv + 1),
                (u1**3) * (v1**3) * (1 + u) * (v + 1) * (u * v - squv + 1) * (u * v + squv + 1),
                (u1**3) * (u - squv + v) * (u + squv + v) * (1 + u) * (v + 1),
                (v1**3) * (u - squv + v) * (u + squv + v) * (1 + u) * (v + 1),
                2 * u1 * v1 * (u + squv + v) * (u * v - squv + 1),
                2 * u1 * v1 * (u - squv + v) * (u * v + squv + 1)]
    if typ[0] == 'F':
        u, v = vs[0], vs[2]
        if u == 1 or u == -1:
            u1 = u
        else:
            u1 = u**(-1)
        if v == 1 or v == -1:
            v1 = v
        else:
            v1 = v**(-1)
        return [(u + 1) * (u**2 + u + 1) * (v + 1) * (v**2 + v + 1) * (u**2 * v + 1) * (u**2 * v**2 + 1) *
                (u * v**2 + 1) * (u**2 * v**2 - u * v + 1) * (u * v + 1)**2,
                (v1**12) * (u + v)**2 * (u**2 - u * v + v**2) * (u**2 + v**2) * (u + v**2) *
                (u**2 + v) * (u + 1) * (u**2 + u + 1) * (v + 1) * (v**2 + v + 1),
                (u1**12) * (u + v)**2 * (u**2 - u * v + v**2) * (u**2 + v**2) * (u + v**2) *
                (u**2 + v) * (u + 1) * (u**2 + u + 1) * (v + 1) * (v**2 + v + 1),
                (u1**12) * (v1**12) * (u + 1) * (u**2 + u + 1) * (v + 1) * (v**2 + v + 1) * (u**2 * v
                 + 1) * (u**2 * v**2 + 1) * (u * v**2 + 1) * (u**2 * v**2 - u * v + 1) * (u * v + 1)**2,
                (v1**3) * (u + 1)**2 * (u**2 + u + 1) * (v**2 + v + 1) * (u * v + 1) * (u**2 * v + 1) *
                (u**2 - u + 1) * (u + v) * (u**2 + v),
                (u1**12) * (v1**3) * (u + 1)**2 * (u**2 + u + 1) * (v**2 + v + 1) * (u * v + 1) *
                (u**2 * v + 1) * (u**2 - u + 1) * (u + v) * (u**2 + v),
                (u1**3) * (u**2 + u + 1) * (v + 1)**2 * (v**2 + v + 1) * (u * v + 1) * (u * v**2 + 1) *
                (v**2 - v + 1) * (u + v) * (u + v**2),
                (u1**3) * (v1**12) * (u**2 + u + 1) * (v + 1)**2 * (v**2 + v + 1) * (u * v + 1) *
                (u * v**2 + 1) * (v**2 - v + 1) * (u + v) * (u + v**2),
                2 * (u1**3) * (v1**3) * (u**2 + u + 1) * (v**2 + v + 1) * (u * v + 1)**2 * (u + v)**2,
                (u1**2) * (v1**2) * (u**2 + v) * (u + v**2) * (u + 1) * (v + 1) * (u**2 * v**2 + 1) *
                (u * v + 1)**2,
                (u1**2) * (v1**6) * (u**2 + v**2) * (u + v)**2 * (u + 1) * (v + 1) * (u**2 * v + 1) *
                (u * v**2 + 1),
                (u1**6) * (v1**2) * (u**2 + v**2) * (u + v)**2 * (u + 1) * (v + 1) * (u**2 * v + 1) *
                (u * v**2 + 1),
                (u1**6) * (v1**6) * (u**2 + v) * (u + v**2) * (u + 1) * (v + 1) * (u**2 * v**2 + 1) *
                (u * v + 1)**2,
                3 * (u1**3) * (v1**3) * (u + 1)**2 * (v + 1)**2 * (u * v + 1)**2 *
                (u**2 - u * v + v**2),
                3 * (u1**3) * (v1**3) * (u + 1)**2 * (v + 1)**2 * (u**2 * v**2 - u * v + 1) *
                (u + v)**2,
                6 * (u1**3) * (v1**3) * (u * v + 1)**2 * (v**2 - v + 1) * (u**2 - u + 1) * (u + v)**2,
                u1 * v1 * (u + v) * (u + 1) * (u**2 + u + 1) * (v + 1) * (v**2 + v + 1) *
                (u**2 * v**2 - u * v + 1) * (u * v + 1)**2,
                u1 * (v1**7) * (u + 1) * (u**2 + u + 1) * (v + 1) * (v**2 + v + 1) * (u * v + 1) *
                (u + v)**2 * (u**2 - u * v + v**2),
                (u1**7) * v1 * (u + 1) * (u**2 + u + 1) * (v + 1) * (v**2 + v + 1) * (u * v + 1) *
                (u + v)**2 * (u**2 - u * v + v**2),
                u1**7 * v1**7 * (u + v) * (u + 1) * (u**2 + u + 1) * (v + 1) * (v**2 + v + 1) *
                (u**2 * v**2 - u * v + 1) * (u * v + 1)**2,
                u1 * (v1**3) * (u + v**2) * (u + 1)**2 * (u**2 - u + 1) * (u**2 + u + 1) *
                (v**2 + v + 1) * (u * v**2 + 1),
                (u1**7) * (v1**3) * (u + v**2) * (u + 1)**2 * (u**2 - u + 1) * (u**2 + u + 1) *
                (v**2 + v + 1) * (u * v**2 + 1),
                (u1**3) * v1 * (u**2 + v) * (v + 1)**2 * (v**2 - v + 1) * (u**2 + u + 1) *
                (v**2 + v + 1) * (u**2 * v + 1),
                (u1**3) * (v1**7) * (u**2 + v) * (v + 1)**2 * (v**2 - v + 1) * (u**2 + u + 1) *
                (v**2 + v + 1) * (u**2 * v + 1),
                2 * (u1**3) * (v1**3) * (u**2 + u + 1) * (v**2 + v + 1) * (u**2 * v**2 + 1) *
                (u**2 + v**2)]
    if typ[0] == 'I':
        m = int(typ[1:])
        if m == 5:
            ir5 = ir(5)
            u = vs[0]**2
            if u == 1 or u == -1:
                u1 = u
            else:
                u1 = u**(-1)
            p2 = u + 1
            p5 = u**4 + u**3 + u**2 + u + 1
            p5a = u**2 + ir5 * u + 1
            p5b = u**2 + (1 - ir5) * u + 1
            vcyc = [u**(0) * p2 * p5, (u1**5) * p2 * p5, (2 + ir5) * u1 * p5b, (3 - ir5) * u1 * p5a]
        else:
            W = coxeter(typ, n)
            ti = heckechartable(W, [vs[0], vs[1]])['irreducibles']
            t = matmult(ti, transposemat(heckecentraltable(W, [vs[0], vs[1]])))
            vcyc = [t[i][i] for i in range(len(ti))]
        return vcyc
    u = vs[0]  # now types E, H
    if u == 1:
        W = coxeter(typ, n)
        ti = chartable(W)['irreducibles']
        return [(W.order // d[0]) * u**0 for d in ti]
    # p1 = u-1
    p2 = u + 1
    p3 = u**2 + u + 1
    p4 = u**2 + 1
    p5 = u**4 + u**3 + u**2 + u + 1
    p6 = u**2 - u + 1
    p7 = u**6 + u**5 + u**4 + u**3 + u**2 + u + 1
    p8 = u**4 + 1
    p9 = u**6 + u**3 + 1
    p10 = u**4 - u**3 + u**2 - u + 1
    # p11 = u**10+u**9+u**8+u**7+u**6+u**5+u**4+u**3+u**2+u+1
    p12 = u**4 - u**2 + 1
    # p13 = u**12+u**11+u**10+u**9+u**8+u**7+u**6+u**5+u**4+u**3+u**2+u+1
    p14 = u**6 - u**5 + u**4 - u**3 + u**2 - u + 1
    p15 = u**8 - u**7 + u**5 - u**4 + u**3 - u + 1
    p18 = u**6 - u**3 + 1
    p20 = u**8 - u**6 + u**4 - u**2 + 1
    p24 = u**8 - u**4 + 1
    p30 = u**8 + u**7 - u**5 - u**4 - u**3 + u + 1

    if typ[0] == 'E' and n == 6:
        return [u**(0) * p2**4 * p3**3 * p4**2 * p5 * p6**2 * p8 * p9 * p12,
              u**(-36) * p2**4 * p3**3 * p4**2 * p5 * p6**2 * p8 * p9 * p12,
              3 * u**(-7) * p2**4 * p3**3 * p4**2, u**(-1) *
                p2**4 * p3**3 * p4**2 * p5 * p6**2 * p12,
              u**(-25) * p2**4 * p3**3 * p4**2 * p5 * p6**2 *
                p12, 6 * u**(-7) * p2**4 * p3**3 * p12,
              2 * u**(-3) * p2**4 * p3**3 * p4**2 * p12, 2 * u**(-15) * p2**4 * p3**3 * p4**2 * p12,
              2 * u**(-3) * p2**4 * p3**3 * p4**2 * p6**2,
              2 * u**(-15) * p2**4 * p3**3 * p4**2 * p6**2,
              u**(-2) * p2**4 * p3**3 * p4 * p6**2 * p9, u**(-20) * p2**4 * p3**3 * p4 * p6**2 * p9,
              u**(-6) * p2**4 * p3**3 * p5 * p6**2, u**(-12) * p2**4 * p3**3 * p5 * p6**2,
              2 * u**(-3) * p2**4 * p3**3 * p6**2 * p8, 2 * u**(-15) * p2**4 * p3**3 * p6**2 * p8,
              2 * u**(-7) * p2**4 * p3**3 * p6**2, 6 * u**(-7) * p3**3 * p4**2 * p6**2,
              3 * u**(-7) * p2**4 * p4**2 * p9, u**(-5) * p2**4 * p3**3 * p4 * p6**2,
              u**(-11) * p2**4 * p3**3 * p4 * p6**2, u**(-4) * p2 * p3**3 * p5 * p9,
              u**(-13) * p2 * p3**3 * p5 * p9, u**(-6) * p2**4 * p4**2 * p5 * p8,
              u**(-10) * p2**4 * p4**2 * p5 * p8]
    if typ[0] == 'E' and n == 7:
        return [u**(0) * p2**7 * p3**3 * p4**2 * p5 * p6**3 * p7 * p8 * p9 * p10 * p12 * p14 * p18,
              u**(-63) * p2**7 * p3**3 * p4**2 * p5 * p6**3 * p7 * p8 * p9 * p10 * p12 * p14 * p18,
              u**(-46) * p2**7 * p3**3 * p4**2 * p5 * p6**3 * p8 * p9 * p10 * p18,
              u**(-1) * p2**7 * p3**3 * p4**2 * p5 * p6**3 * p8 * p9 * p10 * p18,
              2 * u**(-25) * p2**7 * p3**3 * p4**2 * p6**3 * p7,
              2 * u**(-4) * p2**7 * p3**3 * p4**2 * p6**3 * p7,
              2 * u**(-3) * p2**7 * p3**3 * p4**2 * p5 * p6**3 * p18,
              2 * u**(-30) * p2**7 * p3**3 * p4**2 * p5 * p6**3 * p18,
              u**(-36) * p2**7 * p3**3 * p4**2 * p5 * p6**3 * p8 * p10 * p12,
              u**(-3) * p2**7 * p3**3 * p4**2 * p5 * p6**3 * p8 * p10 * p12,
              u**(-2) * p2**7 * p3 * p4**2 * p5 * p6 * p7 * p8 * p10 * p14,
              u**(-37) * p2**7 * p3 * p4**2 * p5 * p6 * p7 * p8 * p10 * p14,
              6 * u**(-16) * p2**7 * p3**3 * p4**2 * p18, 6 * u**(-7) * p2**7 * p3**3 * p4**2 * p18,
              2 * u**(-3) * p2**7 * p3**3 * p4**2 * p6**3 * p9 * p10,
              2 * u**(-30) * p2**7 * p3**3 * p4**2 * p6**3 * p9 * p10,
              2 * u**(-30) * p2**3 * p3**3 * p4**2 * p5 * p6 * p8 * p9 * p12,
              2 * u**(-3) * p2**3 * p3**3 * p4**2 * p5 * p6 * p8 * p9 * p12,
              3 * u**(-16) * p2**7 * p3**3 * p4**2 * p6**3,
              3 * u**(-7) * p2**7 * p3**3 * p4**2 * p6**3,
              2 * u**(-10) * p2**7 * p3**3 * p5 * p6**3, 2 * u**(-13) * p2**7 * p3**3 * p5 * p6**3,
              2 * u**(-25) * p2**7 * p3**3 * p4**2 * p6**3 * p14,
              2 * u**(-4) * p2**7 * p3**3 * p4**2 * p6**3 * p14,
              u**(-6) * p2**7 * p3**3 * p4**2 * p6**3 * p8,
              u**(-21) * p2**7 * p3**3 * p4**2 * p6**3 * p8,
              u**(-12) * p2**7 * p3**3 * p4**2 * p6**3 * p8,
              u**(-15) * p2**7 * p3**3 * p4**2 * p6**3 * p8,
              2 * u**(-4) * p2**3 * p3**3 * p4**2 * p6 * p7 * p8 * p12,
              2 * u**(-25) * p2**3 * p3**3 * p4**2 * p6 * p7 * p8 * p12,
              u**(-6) * p2**7 * p3**3 * p5 * p6**3 * p10,
              u**(-21) * p2**7 * p3**3 * p5 * p6**3 * p10, 2 *
                u**(-8) * p2**7 * p3 * p4**2 * p5 * p14,
              2 * u**(-15) * p2**7 * p3 * p4**2 * p5 * p14,
              u**(-22) * p2**7 * p3 * p4**2 * p5 * p6 * p8 * p10,
              u**(-5) * p2**7 * p3 * p4**2 * p5 * p6 * p8 * p10,
              u**(-20) * p2**7 * p3 * p4**2 * p5 * p6 * p8 * p10,
              u**(-7) * p2**7 * p3 * p4**2 * p5 * p6 * p8 * p10,
              u**(-6) * p2**7 * p3**3 * p4**2 * p6**3 * p12,
              u**(-21) * p2**7 * p3**3 * p4**2 * p6**3 * p12,
              u**(-10) * p2**7 * p3**3 * p4**2 * p6**3,
              u**(-13) * p2**7 * p3**3 * p4**2 * p6**3,
              2 * u**(-15) * p2**3 * p3 * p4**2 * p5 * p7 * p8,
              2 * u**(-8) * p2**3 * p3 * p4**2 * p5 * p7 * p8, 3 *
                u**(-16) * p2**7 * p3**3 * p6**3 * p12,
              3 * u**(-7) * p2**7 * p3**3 * p6**3 * p12, 2 *
                u**(-7) * p2**3 * p3**3 * p4**2 * p8 * p9,
              2 * u**(-16) * p2**3 * p3**3 * p4**2 * p8 * p9, 6 *
                u**(-16) * p2**7 * p4**2 * p6**3 * p9,
              6 * u**(-7) * p2**7 * p4**2 * p6**3 * p9,
              2 * u**(-13) * p2**3 * p3**3 * p4**2 * p5 * p6 * p12,
              2 * u**(-10) * p2**3 * p3**3 * p4**2 * p5 * p6 * p12,
              u**(-14) * p2**7 * p3 * p4**2 * p5 * p6 * p10,
              u**(-9) * p2**7 * p3 * p4**2 * p5 * p6 * p10, 2 * u**(-8) * p2**7 * p4**2 * p6 * p7 * p10,
              2 * u**(-15) * p2**7 * p4**2 * p6 * p7 * p10, 2 *
                u**(-10) * p2**7 * p3**3 * p6**3 * p10,
              2 * u**(-13) * p2**7 * p3**3 * p6**3 * p10, 2 * u**(-11) * p3**3 * p5 * p7 * p9,
              2 * u**(-11) * p3**3 * p5 * p7 * p9]
    if typ[0] == 'E' and n == 8:
        return [u**(0) * p2**8 * p3**4 * p4**4 * p5**2 * p6**4 * p7 * p8**2 * p9 * p10**2 * p12**2 *
              p14 * p15 * p18 * p20 * p24 * p30,
              u**(-120) * p2**8 * p3**4 * p4**4 * p5**2 * p6**4 * p7 * p8**2 * p9 * p10**2 * p12**2 *
               p14 * p15 * p18 * p20 * p24 * p30,
              2 * u**(-3) * p2**8 * p3**4 * p4**2 * p5**2 * p6**4 * p8 * p9 * p10**2 * p12 * p30,
              2 * u**(-63) * p2**8 * p3**4 * p4**2 * p5**2 * p6**4 * p8 * p9 * p10**2 * p12 * p30,
              u**(-2) * p2**8 * p3**4 * p4**4 * p5 * p6**4 * p8**2 * p9 * p10 * p12**2 * p18 * p24,
              u**(-74) * p2**8 * p3**4 * p4**4 * p5 * p6**4 * p8**2 * p9 * p10 * p12**2 * p18 * p24,
              30 * u**(-16) * p2**8 * p3**4 * p4**4 * p30,
              2 * u**(-4) * p2**8 * p3**4 * p4**4 * p6**4 * p7 * p9 * p10 * p12**2,
              2 * u**(-52) * p2**8 * p3**4 * p4**4 * p6**4 * p7 * p9 * p10 * p12**2,
              2 * u**(-3) * p2**8 * p3**4 * p4**2 * p5**2 * p6**4 * p8 * p10**2 * p12 * p15 * p18,
              2 * u**(-63) * p2**8 * p3**4 * p4**2 * p5**2 * p6**4 * p8 * p10**2 * p12 * p15 * p18,
              8 * u**(-16) * p2**8 * p3**4 * p5**2 * p6**4, 3 * u**(-8) * p2**8 * p3**4 * p4**4 *
                p6**4 * p8**2,
              3 * u**(-32) * p2**8 * p3**4 * p4**4 * p6**4 * p8**2,
              2 * u**(-4) * p2**8 * p3**4 * p4**4 * p5 * p6**4 * p12**2 * p14 * p18,
              2 * u**(-52) * p2**8 * p3**4 * p4**4 * p5 * p6**4 * p12**2 * p14 * p18,
              5 * u**(-16) * p2**8 * p3**4 * p4**4 * p6**4,
              2 * u**(-6) * p2**8 * p3**4 * p4**2 * p6**4 * p7 * p8 * p12 * p18,
              2 * u**(-42) * p2**8 * p3**4 * p4**2 * p6**4 * p7 * p8 * p12 * p18,
              6 * u**(-8) * p2**8 * p3**4 * p4**4 * p6**4 * p24, 6 * u**(-32) * p2**8 * p3**4 *
               p4**4 * p6**4 * p24,
              u**(-12) * p2**8 * p3**4 * p4**4 * p6**4 * p8**2 * p12**2,
              u**(-36) * p2**8 * p3**4 * p4**4 * p6**4 * p8**2 * p12**2,
              u**(-6) * p2**8 * p3 * p4**4 * p5**2 * p6 * p8**2 * p10**2 * p20,
              u**(-46) * p2**8 * p3 * p4**4 * p5**2 * p6 * p8**2 * p10**2 * p20,
              6 * u**(-16) * p2**8 * p4**4 * p5**2 * p6 * p18,
              2 * u**(-13) * p2**8 * p3**4 * p4**2 * p6**4 * p8 * p9,
              2 * u**(-25) * p2**8 * p3**4 * p4**2 * p6**4 * p8 * p9,
              2 * u**(-6) * p2**8 * p3**4 * p4**2 * p6**4 * p8 * p9 * p12 * p14,
              2 * u**(-42) * p2**8 * p3**4 * p4**2 * p6**4 * p8 * p9 * p12 * p14,
              24 * u**(-16) * p2**8 * p3**4 * p10**2 * p12**2,
              2 * u**(-12) * p2**8 * p3**4 * p4**2 * p5 * p6**4 * p12,
              2 * u**(-24) * p2**8 * p3**4 * p4**2 * p5 * p6**4 * p12,
              20 * u**(-16) * p2**8 * p3**4 * p6**4 * p20,
              2 * u**(-10) * p2**8 * p4**2 * p5**2 * p6 * p7 * p8 * p10**2,
              2 * u**(-30) * p2**8 * p4**2 * p5**2 * p6 * p7 * p8 * p10**2,
              2 * u**(-8) * p2**8 * p3**4 * p4**4 * p6**4 * p12**2,
              2 * u**(-32) * p2**8 * p3**4 * p4**4 * p6**4 * p12**2,
              u**(-20) * p2**8 * p3**4 * p4**4 * p6**4 * p12**2,
              2 * u**(-7) * p2**4 * p3**4 * p4**2 * p5**2 * p6**2 * p8 * p12 * p15,
              2 * u**(-37) * p2**4 * p3**4 * p4**2 * p5**2 * p6**2 * p8 * p12 * p15,
              8 * u**(-16) * p3**4 * p4**4 * p5**2 * p12**2,
              6 * u**(-8) * p2**8 * p3**4 * p6**4 * p8**2 * p12**2,
              6 * u**(-32) * p2**8 * p3**4 * p6**4 * p8**2 * p12**2,
              3 * u**(-8) * p2**8 * p3 * p4**4 * p6 * p8**2 * p9 * p18,
              3 * u**(-32) * p2**8 * p3 * p4**4 * p6 * p8**2 * p9 * p18,
              6 * u**(-16) * p2**8 * p3 * p4**4 * p9 * p10**2,
              2 * u**(-13) * p2**8 * p3**4 * p4**2 * p6**4 * p8 * p18,
              2 * u**(-25) * p2**8 * p3**4 * p4**2 * p6**4 * p8 * p18,
              8 * u**(-16) * p2**8 * p3**4 * p6**4 * p10**2,
              2 * u**(-10) * p2**4 * p3**4 * p4**2 * p5 * p6**2 * p8 * p9 * p12,
              2 * u**(-28) * p2**4 * p3**4 * p4**2 * p5 * p6**2 * p8 * p9 * p12,
              120 * u**(-16) * p3**4 * p4**4 * p6**4 * p10**2,
              2 * u**(-10) * p2**8 * p3 * p4**2 * p5**2 * p8 * p10**2 * p14,
              2 * u**(-30) * p2**8 * p3 * p4**2 * p5**2 * p8 * p10**2 * p14,
              24 * u**(-16) * p2**8 * p5**2 * p6**4 * p12**2,
              u**(-14) * p2**8 * p3 * p4**4 * p5 * p6 * p8**2 * p10,
              u**(-22) * p2**8 * p3 * p4**4 * p5 * p6 * p8**2 * p10,
              30 * u**(-16) * p2**8 * p4**4 * p6**4 * p15,
              2 * u**(-15) * p2**4 * p3**4 * p4**2 * p6**2 * p7 * p9 * p12,
              2 * u**(-21) * p2**4 * p3**4 * p4**2 * p6**2 * p7 * p9 * p12,
              2 * u**(-11) * p2 * p3**4 * p5**2 * p7 * p9 * p15,
              2 * u**(-26) * p2 * p3**4 * p5**2 * p7 * p9 * p15,
              2 * u**(-12) * p2**8 * p3**4 * p4**2 * p6**4 * p10 * p12,
              2 * u**(-24) * p2**8 * p3**4 * p4**2 * p6**4 * p10 * p12,
              u**(-14) * p2**8 * p4**4 * p7 * p8**2 *
                p14, u**(-22) * p2**8 * p4**4 * p7 * p8**2 * p14,
              u**(-1) * p2**8 * p3**4 * p4**2 * p5**2 * p6**4 * p7 * p8 * p9 * p10**2 * p12 * p14 *
               p15 * p18 * p30,
              u**(-91) * p2**8 * p3**4 * p4**2 * p5**2 * p6**4 * p7 * p8 * p9 * p10**2 * p12 * p14 *
               p15 * p18 * p30,
              6 * u**(-7) * p2**8 * p3**4 * p4**2 * p5**2 * p6**4 * p30,
              6 * u**(-37) * p2**8 * p3**4 * p4**2 * p5**2 * p6**4 * p30,
              2 * u**(-3) * p2**4 * p3**4 * p4**4 * p5**2 * p6**2 * p8 * p9 * p12**2 * p15 * p20,
              2 * u**(-63) * p2**4 * p3**4 * p4**4 * p5**2 * p6**2 * p8 * p9 * p12**2 * p15 * p20,
              2 * u**(-4) * p2**4 * p3**4 * p4**2 * p5 * p6**2 * p7 * p8**2 * p9 * p12 * p24,
              2 * u**(-52) * p2**4 * p3**4 * p4**2 * p5 * p6**2 * p7 * p8**2 * p9 * p12 * p24,
              12 * u**(-16) * p2**4 * p3**4 * p4**2 * p5**2 * p24,
              2 * u**(-6) * p2**4 * p3**4 * p4**4 * p6**2 * p7 * p8 * p9 * p12**2,
              2 * u**(-42) * p2**4 * p3**4 * p4**4 * p6**2 * p7 * p8 * p9 * p12**2,
              3 * u**(-7) * p2**8 * p3**4 * p5**2 * p6**4 * p10**2 * p12,
              3 * u**(-37) * p2**8 * p3**4 * p5**2 * p6**4 * p10**2 * p12,
              u**(-5) * p2**8 * p3**4 * p4**2 * p5 * p6**4 * p9 * p10 * p12 * p18,
              u**(-47) * p2**8 * p3**4 * p4**2 * p5 * p6**4 * p9 * p10 * p12 * p18,
              4 * u**(-16) * p2**4 * p3**4 * p4**2 * p5**2 * p6**2 * p12,
              2 * u**(-10) * p2**8 * p3**4 * p4**2 * p5 * p6**4 * p18,
              2 * u**(-28) * p2**8 * p3**4 * p4**2 * p5 * p6**4 * p18,
              3 * u**(-7) * p2**8 * p3 * p4**2 * p5**2 * p6 * p9 * p10**2 * p18,
              3 * u**(-37) * p2**8 * p3 * p4**2 * p5**2 * p6 * p9 * p10**2 * p18,
              6 * u**(-16) * p2**4 * p3 * p4**2 * p5**2 * p8**2 * p9,
              2 * u**(-10) * p2**4 * p3 * p4**4 * p5**2 * p7 * p8 * p20,
              2 * u**(-30) * p2**4 * p3 * p4**4 * p5**2 * p7 * p8 * p20,
              2 * u**(-10) * p2**8 * p3**4 * p4**2 * p6**4 * p9 * p10,
              2 * u**(-28) * p2**8 * p3**4 * p4**2 * p6**4 * p9 * p10,
              6 * u**(-7) * p2**8 * p3**4 * p4**2 * p6**4 * p10**2 * p15,
              6 * u**(-37) * p2**8 * p3**4 * p4**2 * p6**4 * p10**2 * p15,
              2 * u**(-15) * p2**8 * p3**4 * p6**4 * p7 * p18,
              2 * u**(-21) * p2**8 * p3**4 * p6**4 * p7 * p18,
              2 * u**(-13) * p2**4 * p3**4 * p4**4 * p8 * p9 * p12**2,
              2 * u**(-25) * p2**4 * p3**4 * p4**4 * p8 * p9 * p12**2,
              6 * u**(-16) * p2**4 * p3**4 * p4**2 * p8**2 * p15,
              u**(-9) * p2**8 * p3 * p4**2 * p5 * p6 * p7 * p8 * p10 * p14,
              u**(-31) * p2**8 * p3 * p4**2 * p5 * p6 * p7 * p8 * p10 * p14,
              2 * u**(-12) * p2**4 * p3**4 * p4**4 * p5 * p6**2 * p12**2,
              2 * u**(-24) * p2**4 * p3**4 * p4**4 * p5 * p6**2 * p12**2,
              12 * u**(-16) * p3**4 * p5**2 * p6**2 * p8**2 * p12,
              2 * u**(-11) * p2 * p3**4 * p5**2 * p7 * p9 * p15,
              2 * u**(-26) * p2 * p3**4 * p5**2 * p7 * p9 * p15,
              u**(-15) * p2**8 * p3**4 * p4**2 * p6**4 * p8 * p12,
              u**(-21) * p2**8 * p3**4 * p4**2 * p6**4 * p8 * p12,
              u**(-13) * p2**8 * p3 * p4**2 * p5**2 * p6 * p8 * p10**2,
              u**(-23) * p2**8 * p3 * p4**2 * p5**2 * p6 * p8 * p10**2,
              2 * u**(-15) * p2**8 * p3**4 * p6**4 * p9 * p14,
              2 * u**(-21) * p2**8 * p3**4 * p6**4 * p9 * p14]
    ir5 = ir(5)
    p5a = u**2 + ir5 * u + 1
    p5b = u**2 + (1 - ir5) * u + 1
    p10a = u**2 - ir5 * u + 1
    p10b = u**2 + (ir5 - 1) * u + 1
    p15a = u**4 - ir5 * u**3 + ir5 * u**2 - ir5 * u + 1
    p15b = u**4 + (ir5 - 1) * u**3 + (1 - ir5) * u**2 + (ir5 - 1) * u + 1
    p20a = u**4 - ir5 * u**2 + 1
    p20b = u**4 + (ir5 - 1) * u**2 + 1
    p30a = u**4 + ir5 * u**3 + ir5 * u**2 + ir5 * u + 1
    p30b = u**4 + (1 - ir5) * u**3 + (1 - ir5) * u**2 + (1 - ir5) * u + 1
    if typ[0] == 'H' and n == 3:
        return [u**(-15) * p2**3 * p3 * p5 * p6 * p10, u**(0) * p2**3 * p3 * p5 * p6 * p10,
              u**(-5) * p2**3 * p3 * p6, u**(-2) * p2**3 * p3 * p6,
              (2 + ir5) * u**(-6) * p2**3 * p10a * p5a, (3 - ir5) * u**(-6) * p2**3 * p10b * p5b,
              (2 + ir5) * u**(-1) * p2**3 * p10a * p5a, (3 - ir5) * u**(-1) * p2**3 * p10b * p5b,
              2 * u**(-3) * p3 * p5, 2 * u**(-3) * p3 * p5]
    if typ[0] == 'H' and n == 4:
        return [u**(0) * p2**4 * p3**2 * p4**2 * p5**2 * p6**2 * p10**2 * p12 * p15 * p20 * p30,
              u**(-60) * p2**4 * p3**2 * p4**2 * p5**2 * p6**2 * p10**2 * p12 * p15 * p20 * p30,
              (2 + ir5) * u**(-1) * p2**4 * p3**2 * p5 * p6**2 * p10 * p10b * p15b * p30b * p5b,
              (2 + ir5) * u**(-31) * p2**4 * p3**2 * p5 * p6**2 * p10 * p10b * p15b * p30b * p5b,
              (3 - ir5) * u**(-1) * p2**4 * p3**2 * p5 * p6**2 * p10 * p10a * p15a * p30a * p5a,
              (3 - ir5) * u**(-31) * p2**4 * p3**2 * p5 * p6**2 * p10 * p10a * p15a * p30a * p5a,
              (30 + 30 * ir5) * u**(-6) * p2**4 * p30b * p5a**2,
              (60 - 30 * ir5) * u**(-6) * p2**4 * p30a * p5b**2,
              8 * u**(-6) * p3**2 * p5**2, 10 * u**(-6) * p3**2 * p4**2 * p5,
              (2 + ir5) * u**(-2) * p2**4 * p4**2 * p5 * p10 * p10b * p20a * p5b,
              (2 + ir5) * u**(-22) * p2**4 * p4**2 * p5 * p10 * p10b * p20a * p5b,
              (3 - ir5) * u**(-2) * p2**4 * p4**2 * p5 * p10 * p10a * p20b * p5a,
              (3 - ir5) * u**(-22) * p2**4 * p4**2 * p5 * p10 * p10a * p20b * p5a,
              10 * u**(-6) * p2**4 * p3**2 * p10, 20 * u**(-6) * p3**2 * p20a * p5a**2,
              20 * u**(-6) * p3**2 * p20b * p5b**2, 2 * u**(-3) * p2 * p3**2 * p5**2 * p15,
              2 * u**(-18) * p2 * p3**2 * p5**2 * p15, 2 * u**(-3) * p2 * p3**2 * p5**2 * p15,
              2 * u**(-18) * p2 * p3**2 * p5**2 * p15, 10 * u**(-6) * p2**4 * p5 * p6**2,
              (150 - 90 * ir5) * u**(-6) * p4**2 * p15b * p5a**2,
              (60 + 90 * ir5) * u**(-6) * p4**2 * p15a * p5b**2,
              (1560 - 960 * ir5) * u**(-6) * p6**2 * p10b**2 * p5a**2,
              (600 + 960 * ir5) * u**(-6) * p6**2 * p10a**2 * p5b**2,
              u**(-4) * p2**4 * p3**2 * p4**2 * p6**2 * p12,
              u**(-16) * p2**4 * p3**2 * p4**2 * p6**2 * p12,
              (60 - 30 * ir5) * u**(-6) * p2**4 * p10b**2 * p15a,
              (30 + 30 * ir5) * u**(-6) * p2**4 * p10a**2 * p15b,
              u**(-5) * p2**4 * p5**2 * p10**2, u**(-15) * p2**4 * p5**2 * p10**2,
              40 * u**(-6) * p3**2 * p10**2, 12 * u**(-6) * p5**2 * p12]

# F schurelms


def schurelms(W, paramL):
    r"""returns the Schur elements of an Iwahori-Hecke algebra associated
    with a finite Coxeter group and a list of parameters.  These  are
    uniquely determined by the relations::

                                            /  1 if w=1,
            sum_chi chi(T_w)*s_chi**(-1) =
                                            \  0 otherwise;

    here, the sum runs over all irreducible characters of the Iwahori-
    Hecke algebra and s_chi denotes the corresponding Schur  elements.

    See also 'heckechartable' (for explanations of the conventions for
    the parameters) and 'lcmschurelms'.

    >>> W = coxeter("B", 2)
    >>> v = lpol([1], 1, 'v')       # the built-in Lauent polynomials

    >>> schurelms(W, v)          # equal parameters
    [2*v**(-2)+4+2*v**2,
     2*v**(-2)+2*v**2,
     v**(-8)+2*v**(-6)+2*v**(-4)+2*v**(-2)+1,
     1+2*v**2+2*v**4+2*v**6+v**8,
     2*v**(-2)+4+2*v**2]

    >>> schurelms(W, [v**3, v**2]) # unequal parameters
    [v**(-8)+v**(-6)+v**(-4)+2*v**(-2)+1+v**2+v**4,
     v**(-6)+v**(-4)+v**4+v**6,
     v**(-20)+v**(-16)+v**(-14)+2*v**(-10)+v**(-6)+v**(-4)+1,
     1+v**4+v**6+2*v**10+v**14+v**16+v**20,
     v**(-4)+v**(-2)+1+2*v**2+v**4+v**6+v**8]

    Typically, the parameters will be powers of an indeterminate  (and
    the program has been tested for this case particularly). But it is
    also possible to  take any  non-zero and invertible elements  in a
    commutative ring.  In such a case, it may happen that the function
    returns an error (because  it is running in difficulties with some
    divisions). To get around  this, first  compute the Schur elements
    generically, and then  evaluate  the resulting polynomials  at the
    desired values.

    >>> [s.value(rootof1(6)) for s in schurelms(coxeter("B", 4), v)]
    [0, 0, -4+4*E(6), 0, 0, 2, 1, 0, 0, -2, 4*E(6), 0, -4*E(6),
                                           0, 4-4*E(6), 0, 0, 2, 0, 0]
    """
    if isinstance(paramL, list):
        vs = paramL[:]
    else:
        vs = len(W.rank) * [paramL]
    ct = W.cartantype[0]
    if ct[0] == 'G':
        schur = schurelmdata(ct[0], len(ct[1]), [vs[ct[1][0]]**2, vs[ct[1][1]]**2,
                                                 vs[ct[1][0]] * vs[ct[1][1]]])
    elif ct[0][0] == 'I':
        schur = schurelmdata(ct[0], len(ct[1]), [vs[ct[1][0]], vs[ct[1][1]]])
    else:
        schur = schurelmdata(ct[0], len(ct[1]), [vs[s]**2 for s in ct[1]])
    for ct in W.cartantype[1:]:
        if ct[0] == 'G':
            s1 = schurelmdata(ct[0], len(ct[1]), [vs[ct[1][0]]**2, vs[ct[1][1]]**2,
                                                  vs[ct[1][0]] * vs[ct[1][1]]])
        elif ct[0][0] == 'I':
            s1 = schurelmdata(ct[0], len(ct[1]), [vs[ct[1][0]], vs[ct[1][1]]])
        else:
            s1 = schurelmdata(ct[0], len(ct[1]), [vs[s]**2 for s in ct[1]])
        schur = flatlist([[x * sh for sh in s1] for x in schur])
    return schur

# F lcmschurelms


def lcmschurelms(W, paramL):
    """returns  the least common multiple  of all Schur elements of the
    generic Iwahori-Hecke algebra  associated with  a finite Coxeter
    group and a list of parameters.  In the equal parameter case, it
    is well-known that this is just given by the Poincare polynomial
    multiplied by a constant which is divisible by bad primes only.

    It is  also known that a  specialised  Iwahori-Hecke  algebra is
    semisimple  if and only if  this  least common multiple  remains
    non-zero under the specialisation.

    >>> W = coxeter("B", 2)
    >>> v=lpol([1], 1, 'v')          # the built-in Lauent polynomials
    >>> lcmschurelms(W, v)          # equal parameters
    2+4*v**2+4*v**4+4*v**6+2*v**8
    >>> lcmschurelms(W, [v**2, v])   # unequal parameters
    1+v**2+v**4+2*v**6+v**8+v**10+v**12

    See also 'schurelms' and 'poincarepol'.
    """
    if isinstance(paramL, list):
        vs = paramL[:]
    else:
        vs = len(W.rank) * [paramL]
    lcms = []
    for ct in W.cartantype:
        equ = True
        vs1 = [vs[s] for s in ct[1]]
        for p in vs1[1:]:
            if p != vs1[0]:
                equ = False
        if not equ:
            if ct[0][0] == 'I':
                lprint('#I Just taking product of Schur elements\n')
                sh = schurelms(coxeter(ct[0], len(ct[1])), vs1)
                p = 1
                for se in sh[4:]:
                    p *= se
                p = lcmcyclpol([p, sh[0], sh[1], sh[2], sh[3]])
            else:
                p = lcmcyclpol(schurelms(coxeter(ct[0], len(ct[1])), vs1))
        else:
            p = poincarepol(coxeter(ct[0], len(ct[1])), vs1[0]**2)
            if ct[0] == 'B' or ct[0] == 'C':
                d = 0
                while d * (d + 1) <= len(ct[1]):
                    d += 1
                p = 2**(d - 1) * p
            if ct[0] == 'D':
                d = 0
                while d * d <= len(ct[1]):
                    d += 1
                p = 2**(d - 2) * p
            if ct[0] == 'G':
                p = 6 * p
            if ct[0] == 'F':
                p = 24 * p
            if ct[0] == 'E' and len(ct[1]) == 6:
                p = 6 * p
            if ct[0] == 'E' and len(ct[1]) == 7:
                p = 6 * p
            if ct[0] == 'E' and len(ct[1]) == 8:
                p = 120 * p
            if ct[0] == 'H' and len(ct[1]) == 3:
                p = 10 * p
            if ct[0] == 'H' and len(ct[1]) == 4:
                p = 120 * p
            if ct[0][0] == 'I':
                p = int(ct[0][1:]) * p
        lcms.append(p)
    return lcmcyclpol(lcms)

# F cocharpol


def cocharpol(W, u):
    c = conjugacyclasses(W)
    p = (u - 1)**len(W.rank) * poincarepol(W, u)
    cp = []
    for i in range(len(c['reps'])):
        m = [list(row) for row in W.wordtomat(c['reps'][i])]
        for k in W.rank:
            for l in W.rank:
                if k == l:
                    m[k][k] = u - m[k][k] * u**0
                else:
                    m[k][l] = -m[k][l] * u**0
        cp.append(divmod(p, determinantmat(m))[0])
    return [(-1)**len(c['reps'][i]) * c['classlengths'][i] * cp[i]
            for i in range(len(cp))]

# F fakedegree


def fakedegree(W, u, chars):
    """returns the fake degrees of characters  of a finite Coxeter group.

    Given an arbitrary class function f, the fake degree is defined by::

                                               (-1)^l(w) f(w)
       R(f)=(1/|W|) * P (u-1)^r * sum_{w in W} --------------
                                                det(u.id - w)

    where r denotes the rank of W and P is the Poincare polynomial. We
    always have that R(f) is a polynomial in u, where the coefficients
    are integers if f is a character.

    If f is an irreducible character of W,  then the  b-invariant of f
    is defined to be the largest integer b such that u^b divides R(f).
    The b-invariants are contained in the result of 'chartable(W)'.

    >>> W = coxeter("G", 2)
    >>> v=lpol([1], 1, 'v')
    >>> fakedegree(W, v, chartable(W)['irreducibles'])
    [1, v**6, v**3, v**3, v+v**5, v**2+v**4]
    >>> chartable(W)['b']
    [0, 6, 3, 3, 1, 2]
    """
    cp = cocharpol(W, u)
    return [divmod(sum(char[i] * cp[i] for i in range(len(cp))), W.order)[0]
            for char in chars]

# F fakeomega


def fakeomega(W, u):
    """returns the matrix of all terms

         u^W.N * R( chi tensor chi' tensor sign)

    where chi, chi' run over all irreducible characters of W; see also
    'fakedegree''.  The entries of  this matrix are  polynomials with
    integer coefficients;  furthermore, all principal  minors of this
    matrix are non-zero; see

    M. Geck and G. Malle, On special pieces in the unipotent variety.
                          Experimental Math. 8 (1999), 281--290.

    One application of this matrix is the (conjectural) algorithm for
    computing the sizes of special pieces in the above article. It is
    also used in the algorithm for computing the Green functions of a
    finite (split) reductive group with Weyl group W.  Note  that the
    function also works for W of non-crystallographic type.
    """
    ti = chartable(W)
    cp = cocharpol(W, u)
    om = [len(ti['b']) * [0] for i in ti['b']]
    for i in range(len(ti['b'])):
        for j in range(i, len(ti['b'])):
            char = [ti['irreducibles'][ti['position_sgn']][k] *
                   ti['irreducibles'][i][k] * ti['irreducibles'][j][k]
                    for k in range(len(ti['b']))]
            om[i][j] = u**W.N * divmod(sum(char[i] * cp[i] for i in range(len(cp))),
                                       W.order)[0]
            if i != j:
                om[j][i] = om[i][j]
    return om

# F some mod p functions needed for greenalgo


def repintp(n, p):
    m = n % p
    if m > (p - 1) // 2:
        return m - p
    else:
        return m


def powp(x, n, p):
    y = 1
    for i in range(n):
        y = (y * x) % p
    return y


def matsubp(a, b, p):
    return [[(a[i][j] - b[i][j]) % p for j in range(len(a[0]))]
            for i in range(len(a))]


def matmultp(a, b, p):
    return [[(sum((row[k] * b[k][j]) % p for k in range(len(b)))) % p
             for j in range(len(b[0]))] for row in a]


def valuep(f, x, p):
    if f.coeffs == []:
        return 0
    y = 0
    for i in range(len(f.coeffs)):
        y = ((x * y) % p + f.coeffs[-i - 1]) % p
    for i in range(f.val):
        y = (y * x) % p
    return y


def applychinrem(mat1, mat2, m1, m2):
    """apply Chinese Remainder to a matrix of lists.
    """
    m = m1 * m2
    g = gcdex(m1, m2)
    for i in range(len(mat1)):
        for j in range(len(mat1)):
            for k in range(len(mat1[i][j])):
                x = (mat1[i][j][k] * g['coeff2'] * m2 +
                   mat2[i][j][k] * g['coeff1'] * m1) % m
                if x > (m - 1) // 2:
                    mat1[i][j][k] = x - m
                else:
                    mat1[i][j][k] = x

# F blockLR


def blockLR(mat, bl, diag, p):
    """returns the block LR decomposition of a symmetric matrix with integer
    coefficients modulo a prime:

                P * L * P^{tr} = mat   (mod p)

    where L is a block diagonal matrix  (with blocks  specified  by 'bl')
    and P is  block lower triangular with  diagonal  blocks consisting of
    scalar matrices (with scalars specified by 'diag'). If some principal
    minor of mat is zero modulo p, the function returns 'False'.
    """
    P = [[[] for b in bl] for c in bl]
    L = [[] for b in bl]
    fbl = flatlist(bl)
    for j in range(len(bl)):
        if diag[j] % p == 0:
            return False
        d1 = 1
        while (d1 * diag[j]) % p != 1:
            d1 += 1
        Lj = [[mat[r][s] for s in bl[j]] for r in bl[j]]
        for k in range(j):
            Lj = matsubp(Lj, matmultp(P[j][k], matmultp(L[k],
                                   transposemat(P[j][k]), p), p), p)
        L[j] = [[(((x * d1) % p) * d1) % p for x in r] for r in Lj]
        invj = inversematp(L[j], p)
        if invj is False:
            return False
        for i in range(len(bl)):
            if i < j:
                P[i][j] = [len(bl[j]) * [0] for r in bl[i]]
            elif i == j:
                P[j][j] = idmat(bl[j], diag[j] % p)
            else:
                Pij = [[mat[r][s] % p for s in bl[j]] for r in bl[i]]
                for k in range(j):
                    Pij = matsubp(Pij, matmultp(P[i][k], matmultp(L[k],
                                              transposemat(P[j][k]), p), p), p)
                P[i][j] = matmultp([[(x * d1) % p for x in r] for r in Pij], invj, p)
    # mat1=[[mat[r][s] for s in fbl] for r in fbl]
    # if not all(x%p==0 for x in flatlist(matsubp(matmult(resP,
    #                    matmult(resL, transposemat(resP))), mat1)), p):
    #  print("grosser mist!")
    return [flatblockmat(P), reduce(directsummat, L), fbl]

# F greenalgo


def greenalgo(W, u, fam, avals, check=True, startpr=0, verbose=False):
    """applies generalised version of the algorithm for computing Green
    functions.
    """
    gom = fakeomega(W, u)
    fbl = flatlist(fam)
    if startpr == 0:
        p = max(2 * sum(W.degrees) + 2, 800)
    else:
        p = startpr
    fertig = False
    if verbose:
        lprint('#I Prime: ')
    while not fertig:
        p = nextprime(p + 100)
        Ps, Ls = [], []
        if verbose:
            lprint(str(p) + '; ')
        i = 2
        l = []
        while i <= 2 * p and len(l) <= 2 * sum(W.degrees) + 2:
            omp = [[valuep(f, i, p) for f in row] for row in gom]
            if len(l) % 10 == 0:
                if verbose:
                    lprint(str(len(l)) + ' ')
            ap = []
            for a in avals:
                x = 1
                for e in range(a):
                    x = (x * i) % p
                ap.append(x)
            bl = blockLR(omp, fam, ap, p)
            if bl is not False:
                l.append(i)
                Ps.append(bl[0])
                Ls.append(bl[1])
            if i > 0:
                i = -i
            else:
                i = 1 - i
        if verbose:
            lprint('\n')
            lprint('#I Now interpolating ')
        vm = inversematp([[powp(x, i, p) for x in l] for i in range(len(l))], p)
        if vm is not False:
            P, L = idmat(fbl, 0), idmat(fbl, 0)
            for i in range(len(fbl)):
                if i % 5 == 0:
                    if verbose:
                        lprint('.')
                for j in range(len(fbl)):
                    if j <= i and any(m[i][j] != 0 for m in Ps):
                        coeffs0 = matmultp([[m[i][j] for m in Ps]], vm, p)[0]
                        P[i][j] = lpol([repintp(c, p) for c in coeffs0], 0, v.vname)
                    if any(m[i][j] != 0 for m in Ls):
                        coeffs1 = matmultp([[m[i][j] for m in Ls]], vm, p)[0]
                        L[i][j] = lpol([repintp(c, p) for c in coeffs1], 0, v.vname)
            fertig = True
            if verbose:
                lprint('\n#I Checking: ')
            i = 0
            while fertig and i < len(fbl):
                if verbose and not i % 5:
                    lprint(str(i) + ' ')
                j = 0
                while fertig and j <= i:
                    x = sum(P[j][s] * sum(P[i][r] * L[r][s] for r in range(i + 1)
                                  if L[r][s] != 0) for s in range(j + 1) if P[j][s] != 0)
                    if x != gom[fbl[i]][fbl[j]]:
                        if verbose:
                            lprint(' ... change prime ...')
                        fertig = False
                    j += 1
                i += 1
        if verbose:
            lprint(' ' + str(fertig) + ' ')
    if verbose:
        lprint('\n')
    return [P, L, fbl]

# F specialpieces


def specialpieces(W, v, verbose=False):
    """returns  the polynomials giving the sizes of Lusztig's special pieces,
    computed by the algorithm described in

      M. Geck and G. Malle, On special pieces in the unipotent variety.
                            Experimental Math. 8 (1999), 281--290.

    The function returns a list of pairs (chi, s)  where chi runs over the
    special characters of W and s is the polynomial giving the size of the
    special  piece  associated  with  chi.  The  total size of all special
    pieces should be v^(2*N) where N is the number of positive roots.

    >>> W = coxeter("H", 3)
    >>> v=lpol([1], 1, 'v')      # built-in polynomials
    >>> specialpieces(W, v)
    [[("1_r'",), 1],
     [('3_s',), -1-v**4-v**8+v**10+v**14+v**18],
     [("5_r'",), v**4-v**10-v**14+v**20],
     [("4_r'",), v**8-v**14-v**18+v**24],
     [('5_r',), v**10-v**16-v**20+v**26],
     [("3_s'",), -v**10+v**12+v**16-v**18+v**20-v**22-v**26+v**28],
     [('1_r',), -v**12+v**14+v**18-v**20+v**22-v**24-v**28+v**30]]
    """
    ti = chartable(W)
    a1 = list(set(ti['a']))
    a1.sort(reverse=True)
    g = greenalgo(W, v, [list(filter(lambda i:ti['a'][i] == x,
                        range(len(ti['a'])))) for x in a1], a1)
    spec = []
    tot = 0
    for i in range(len(g[2])):
        ch = g[2][i]
        if ti['a'][ch] == ti['b'][ch]:
            spec.append([ti['charnames'][ch], g[1][i][i]])
            tot += g[1][i][i]
    if verbose:
        lprint('#I Total size of all special pieces: ')
        lprint(repr(tot))
        lprint('\n')
    return spec

##########################################################################
##
# Y Section 4: Kazhdan-Lusztig cells
##

# class-wgraph


class wgraph:
    """creates  a W-graph  (as a python class)  for a finite Coxeter
    group W with respect to a weight function.  This consists of the
    following data:

    * a set X together with a map I which assigns to each x in X
      a subset I(x) of S (the set of generators of W);

    * a collection of elements {m_{x, y}^s} in A, where  x, y in X
      and  s in S are such that  s has weight >0,  s in I(x) and
      s is not in I(y);

    * a bijection s:X -> X for every s in S with weight 0.

    (Here, A is the ring of Laurent polynomials  in one variable,  v
    say.)  These data are subject to the following requirements:  we
    require that:

    * v^L(s)m_{x, y}^s is an actual polynomial with constant term 0;

    * and m_{x, y}(v^(-1)) = m_{x, y}^s for all relevant x, y, s.

    Furthermore, let V be a free A-module with a basis {e_y|y in X}.
    For s in S, define an A-linear map rho_s: V -> V by

      e_y -> -v^{-L(s)} e_y   if s in I(y) and s has weight >0,

      e_y ->  v^L(s) e_y +  sum_{x in X:s in I(x)} m_{x, y}^s e_{x}

                              if s not in I(y) and s has weight >0,

      e_y ->  e_{s.y}         if s has weight 0.

    Then we require that the map T_s->rho_s defines a representation
    of the generic Iwahori-Hecke algebra associated with W, L. Recall
    that the quadratic relations in this algebra are given by

        T_s^2 = T_1 + (v^L(s) - v^(-L(s))) T_s   for all s in S.

    The result of 'wgraph' is a class with the following components:

    - W       -- the underlying group W
    - var     -- the parameter (typically a variable v)
    - X       -- the base set (given as reduced expression in the case
      where the W-graph arises from a left cell)
    - Isets   -- the sets I(x) for x in X
    - mpols   -- the list of all possible m-values
    - mmat    -- a dictionary with keys given by pairs (y, x) where x, y
      in X and  m_{x, y}^s is not  0 for at least some s. If
      (y, x) is such a pair, then the value will be a string
      pointing to the appropriate value in mpols.
    - Xrep    -- a hashable set in bijection with X

    The input to  'wgraph'  can take several forms: For example, one
    can specify explicitly  the above components.  There are further
    possibilities; see 'relklpols' for some examples.

    >>> W = coxeter("G", 2)
    >>> k=klcells(W, 1, v); k[1]
    [wgraph(coxeter('G',2), [1, 1], [[]]),
     wgraph(coxeter('G',2), [1, 1], [[1], [0, 1], [1, 0, 1], [0, 1, 0, 1], [1, 0, 1, 0, 1]]),
     wgraph(coxeter('G',2), [1, 1], [[0], [1, 0], [0, 1, 0], [1, 0, 1, 0], [0, 1, 0, 1, 0]]),
     wgraph(coxeter('G',2), [1, 1], [[0, 1, 0, 1, 0, 1]])]

    The corresponding left cell representations:

    >>> [l.matrices(True) for l in k[1]]
    [[[[v**2]], [[v**2]]],
     [[[-1]], [[-1]]],
     [[[v**2, v, 0, 0, 0],
       [0, -1, 0, 0, 0],
       [0, v, v**2, v, 0],
       [0, 0, 0, -1, 0],
       [0, 0, 0, v, v**2]],
      [[-1, 0, 0, 0, 0],
       [v, v**2, v, 0, 0],
       [0, 0, -1, 0, 0],
       [0, 0, v, v**2, v],
       [0, 0, 0, 0, -1]]],
     [[[-1, 0, 0, 0, 0],
       [v, v**2, v, 0, 0],
       [0, 0, -1, 0, 0],
       [0, 0, v, v**2, v],
       [0, 0, 0, 0, -1]],
      [[v**2, v, 0, 0, 0],
       [0, -1, 0, 0, 0],
       [0, v, v**2, v, 0],
       [0, 0, 0, -1, 0],
       [0, 0, 0, v, v**2]]]]

    See also 'reflectionwgraph', 'klcells' and 'wgraphstarorbit'.
    """

    def __init__(self, W, weightL, xset, v, isets=None, mmat=[], mues=[], xrep=[]):
        if isinstance(weightL, int):
            self.weights = len(W.rank) * [weightL]
        else:
            self.weights = weightL
        uneq = not all(i == 1 for i in self.weights)
        self.W = W
        self.X = xset
        self.var = v
        if isets is not None:
            self.Isets = isets
            self.mpols = mues
            self.mmat = mmat
            self.Xrep = xrep
        else:
            ap = [W.wordtoperm(w) for w in xset['elms']]
            ll = [W.permlength(p) for p in ap]
            self.Isets = [W.leftdescentsetperm(p) for p in ap]
            nmues = [[0, 1] for s in W.rank]
            mm = {}
            for y in range(len(ap)):
                for x in range(y):
                    if xset['klmat'][y][x][0] == 'c':
                        ms = xset['klmat'][y][x].split('c')[2:]
                        mstr = ''
                        if not uneq:
                            for s in W.rank:
                                if s in self.Isets[x] and s not in self.Isets[y]:
                                    if len(ms) == len(W.rank):
                                        if ms[s] != '' and ms[s] != '0':
                                            m = -(-1)**(ll[y] + ll[x]) * \
                                                xset['mpols'][s][int(ms[s])]
                                            if m in nmues[s]:
                                                mstr += 'c' + \
                                                    str(nmues[s].index(m))
                                            else:
                                                mstr += 'c' + str(len(nmues[s]))
                                                nmues[s].append(m)
                                        else:
                                            mstr += 'c0'
                                    else:
                                        if ms[0] != '' and ms[0] != '0':
                                            m = -(-1)**(ll[y] + ll[x]) * \
                                                xset['mpols'][int(ms[0])]
                                            if m in nmues[s]:
                                                mstr += 'c' + \
                                                    str(nmues[s].index(m))
                                            else:
                                                mstr += 'c' + str(len(nmues[s]))
                                                nmues[s].append(m)
                                        else:
                                            mstr += 'c0'
                                else:
                                    mstr += 'c'
                        else:
                            for s in W.rank:
                                if self.weights[s] > 0:
                                    if ms[s] != '' and ms[s] != '0':
                                        m = -(-1)**(ll[y] + ll[x]) * \
                                            xset['mpols'][s][int(ms[s])]
                                        if m in nmues[s]:
                                            mstr += 'c' + str(nmues[s].index(m))
                                        else:
                                            mstr += 'c' + str(len(nmues[s]))
                                            nmues[s].append(m)
                                    else:
                                        mstr += 'c0'
                                else:  # self.weights[s]=0:
                                    sy = tuple([ap[y][i] for i in W.permgens[s]])
                                    if sy in ap and ap[x] == sy:
                                        mstr += 'c1'
                                    else:
                                        mstr += 'c0'
                        if any(i != '0' and i != 'c' for i in mstr):
                            mm[(y, x)] = mstr
                for s in W.rank:
                    if s not in self.Isets[y]:
                        sy = tuple([ap[y][i] for i in W.permgens[s]])
                        if sy in ap:
                            syi = ap.index(sy)
                            mm[(y, syi)] = ''
                            for t in W.rank:
                                if t == s:
                                    mm[(y, syi)] += 'c1'
                                else:
                                    mm[(y, syi)] += 'c0'
            # self.X = [W.permtoword(p) for p in ap]
            self.X = [w[:] for w in xset['elms']]
            self.Xrep = [p[:len(W.rank)] for p in ap]
            self.mpols = nmues
            self.mmat = mm

    def __eq__(self, wgr):
        return self.Xrep == wgr.Xrep

    def __repr__(self):
        return 'wgraph(' + repr(self.W) + ', ' + str(self.weights) + ', ' + str(self.X) + ')'

    def normalise(self):
        """returns  a wgraph  (for the same representation) where the
        base set has been sorted.  If  the  base set  consists  of
        lists, then the lists will be sorted by increasing length.
        Otherwise, a generic 'sort' will be applied.
        """
        lx = self.X[:]
        if isinstance(self.X[0], list):
            lx.sort(key=(lambda x: len(x)))
        else:
            lx.sort()
        if lx == self.X:
            return self
        else:
            l = [self.X.index(x) for x in lx]
            l1 = [l.index(i) for i in range(len(l))]
            x1r = [self.Xrep[i] for i in l]
            i1 = [self.Isets[i] for i in l]
            m1 = {}
            for k in self.mmat:
                m1[(l1[k[0]], l1[k[1]])] = self.mmat[k]
            return wgraph(self.W, self.weights, lx, self.var, i1, m1, self.mpols, x1r)

    def wgraphtoklmat(self):
        """returns  a  dictionary which  can be used as input  to the
        function 'relklpols'. If G is a W-graph, then we have

                G=wgraph(W, 1, G.wgraphtoklmat(), v)

        For examples of the use of this function, see 'relklpols'.
        """
        mat = []
        for j in range(len(self.X)):
            mat.append(['f' for i in range(j + 1)])
        mues = [[0, 1] for s in self.W.rank]
        for j in range(len(self.X)):
            for i in range(j):
                if (j, i) in self.mmat:
                    mstr = 'c0'   # exact value will not be used anywhere
                    eps = -(-1)**(len(self.X[i]) + len(self.X[j]))
                    rk = self.mmat[(j, i)].split('c')[1:]
                    for s in self.W.rank:
                        if rk[s] != '':
                            m = eps * self.mpols[s][int(rk[s])]
                            if m in mues[s]:
                                mstr += 'c' + str(mues[s].index(m))
                            else:
                                mstr += 'c' + str(len(mues[s]))
                                mues[s].append(m)
                        else:
                            mstr += 'c0'
                    mat[j][i] = mstr
        return {'elms': self.X, 'mpols': mues, 'klmat': mat}

    def decompose(self):
        """checks if a W-graph is indecomposable and, if not, returns
        the list of W-graphs of the indecomposable composants.
        """
        pp0 = [[w] for w in range(len(self.X))]
        for p in self.mmat:
            pp0[p[0]].append(p[1])
        pp1 = [p[:] for p in pp0]
        for z in pp1:
            for w in z:
                for y in pp0[w]:
                    if y not in z:
                        z.append(y)
        lcells = []
        rest = list(range(len(self.X)))
        while rest != []:
            l = [x for x in pp1[rest[0]] if rest[0] in pp1[x]]
            l.sort()
            lcells.append(l)
            for w in l:
                rest.remove(w)
        neu = []
        for l in lcells:
            x1 = [self.X[i] for i in l]
            x1r = [self.Xrep[i] for i in l]
            i1 = [self.Isets[i] for i in l]
            m1 = {}
            for k in self.mmat:
                if k[0] in l and k[1] in l:
                    m1[(l.index(k[0]), l.index(k[1]))] = self.mmat[k]
            neu.append(wgraph(self.W, self.weights, x1,
                       self.var, i1, m1, self.mpols, x1r))
        return neu

    def matrices(self, check=False, param='generic', verbose=False):
        """returns  the  representing  matrices for a  W-graph.  Note
        that, here, the  matrices  corresponding  to the  elements
        v**weightL[s] T_s are returned.  (The  advantage  of  this
        convention is that  no inverses of  elements  in the  base
        ring are required.)  If the optional argument  'check'  is
        set  to  'True',  then  the  defining  relations  will  be
        checked. There is a further optional argument 'param'.  It
        can be used to specialise the base parameter. For example,
        setting param=1 yields representing matrices for W itself.
        """
        if param == 'generic':
            v = self.var
        else:
            v = param
        mats = [idmat(self.X, 0) for s in self.W.rank]
        for s in self.W.rank:
            for y in range(len(self.X)):
                if self.weights[s] > 0 and s in self.Isets[y]:
                    mats[s][y][y] = -1
                else:
                    if self.weights[s] > 0:
                        mats[s][y][y] = v**(2 * self.weights[s])
                    for x in range(len(self.X)):
                        if self.weights[s] == 0 or s in self.Isets[x]:
                            if (y, x) in self.mmat:
                                mats[s][y][x] = v**(self.weights[s]) * self.mpols[s][
                                    int(self.mmat[y, x].split('c')[s + 1])]
        if check:
            if verbose:
                lprint('#I defining relations are ')
            for s in self.W.rank:
                sq = v**(2 * self.weights[s])
                if matmult(mats[s], mats[s]) != matadd(idmat(self.X, sq),
                                              scalmatmult(sq - 1, mats[s])):
                    lprint('Mist1!\n')
                    return 'False1'
                for t in range(s + 1, len(self.W.rank)):
                    a = matmult(mats[s], mats[t])
                    b = matmult(mats[t], mats[s])
                    m = self.W.coxetermat[s][t]
                    if m % 2 == 0:
                        a1, b1 = a, b
                        for i in range(m // 2 - 1):
                            a1, b1 = matmult(a1, a), matmult(b1, b)
                    else:
                        a1, b1 = a, b
                        for i in range((m - 1) // 2 - 1):
                            a1, b1 = matmult(a1, a), matmult(b1, b)
                        a1, b1 = matmult(a1, mats[s]), matmult(b1, mats[t])
                    if a1 != b1:
                        lprint('Mist2!\n')
                        return 'False2'
            if verbose:
                lprint('true\n')
        return mats

    def character(self, v=1):
        """returns  the  character  of the  underlying  Coxeter group
        afforded by the W-graph representation. The values are  on
        representatives of minimal length in the conjugacy classes
        of W, as returned by  'conjugacyclasses'.  The result will
        be added as component 'char' to the wgraph class.

        >>> W = coxeter("A", 3)
        >>> [l.character() for l in klcells(W, 1, v)[1]]
        [[1, 1, 1, 1, 1], [3, 1, -1, 0, -1], [3, 1, -1, 0, -1], [2, 0, 2, -1, 0],
         [3, -1, -1, 0, 1], [3, 1, -1, 0, -1], [2, 0, 2, -1, 0],
         [3, -1, -1, 0, 1], [3, -1, -1, 0, 1], [1, -1, 1, 1, -1]]

        Thus, the left cells 0, 1, 3, 4, 9 have pairwise different
        characters and,  hence,  yield  a full set of  irreducible
        representations of W.  (It is known that,  in type A,  all
        left cell representations are irreducible.)
        """
        m = self.matrices(param=v)
        c = [len(m[0])]
        for w in conjugacyclasses(self.W)['reps'][1:]:
            c.append(sum([reduce(matmult, [m[s] for s in w])[i][i]
                          for i in range(c[0])]))
        self.char = c
        return c
# end of definition of class wgraph

# reflectionwgraph


def reflectionwgraph(W, weightL, v):
    """returns the W-graph corresponding to the reflection representation
    of a Coxeter group W with respect to a weight function.

    >>> v = lpol([1], 1, "v")
    >>> reflectionwgraph(coxeter("A", 2), 1, v).matrices(True)
    [[[-v**(-1), 0], [1, v]], [[v, 1], [0, -v**(-1)]]]

    >>> reflectionwgraph(coxeter("G", 2), [7, 1], v).matrices(True)
    [[[-v**(-7), 0], [v**(-6)+1+v**6, v**7]], [[v, 1], [0, -v**(-1)]]]

    (The optional  argument  'True'  forces the function to check  the
    defining relations for the representing matrices.)

    For the conventions regarding the argument specifying the weights,
    see the help of 'ainvariants' for further explanation.

    See also 'wgraph'.
    """
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL
    mues = [[0, 1] for s in W.rank]
    mmat = {}
    for y in W.rank:
        for x in W.rank:
            if W.coxetermat[x][y] != 2 and (poids[x] < poids[y]
                                   or (poids[x] == poids[y] and x < y)):
                mmat[(x, y)] = ''
                mmat[(y, x)] = ''
                for s in W.rank:
                    if s == x:
                        mmat[(y, x)] += 'c1'
                    else:
                        mmat[(y, x)] += 'c0'
                for s in W.rank:
                    if s == y:
                        e = poids[y] - poids[x]
                        m = (W.cartan[x][y] * W.cartan[y][x] - 2) * v**0 + v**e + v**(-e)
                        if m in mues[s]:
                            mmat[(x, y)] += 'c' + str(mues[s].index(m))
                        else:
                            mmat[(x, y)] += 'c' + str(len(mues[s]))
                            mues[s].append(m)
                    else:
                        mmat[(x, y)] += 'c0'
    return wgraph(W, weightL, list(W.rank), v, [[s] for s in W.rank],
                  mmat, mues, W.permgens[:])

# F pospart, nonnegpart, zeropart and barpart needed for klpolynomials


def pospart(f):
    if isinstance(f, int):
        return 0
    if f.val > 0:
        return f
    if len(f.coeffs) > -f.val:
        return lpol([f.coeffs[i] for i in range(-f.val + 1, len(f.coeffs))],
                    1, f.vname)
    return 0


def nonnegpart(f):
    if isinstance(f, int):
        return f
    if f.val >= 0:
        return f
    if len(f.coeffs) >= -f.val:
        return lpol([f.coeffs[i] for i in range(-f.val, len(f.coeffs))],
                    0, f.vname)
    return 0


def zeropart(f):
    if isinstance(f, int):
        return f
    if f.val <= 0 and len(f.coeffs) > -f.val:
        return f.coeffs[-f.val]
    return 0


def barpart(f):
    if isinstance(f, int):
        return f
    return lpol(f.coeffs[::-1], -f.degree, f.vname)


def klpolynomials(W, weightL, v, verbose=False):
    """returns the matrix of all Kazhdan-Lusztig  polynomials,  and further
    information on the corresponding left cells, with respect to a given
    weight function. The result is a dictionary with components:

    - elms   : all elements of W (as reduced words, in increasing order)
    - klpols : the Kazhdan-Lusztig polynomials
    - mpols  : the mue-polynomials
    - klmat  : a matrix indexed by pairs of elements of W,  whose entries
      are strings  encoding  information  on Kazhdan-Lusztig and
      mue polynomials.  If y<=w (Bruhat-Chevalley  order),  then
      klmat[w][y] is of the form  'c<p>c<i0>c<i1> ...' where <p>
      refers to  a polynomial  in 'klpols' and  <i0>, <i1> refer
      to the polynomials in 'mpols' for the generators  labelled
      by 0, 1, ... Otherwise, klmat[w][y] equals 'f'.
    - arrows : a complete list of all pairs (w, y) where y, w in W are such
      that C_y occurs in C_sC_w for some simple reflection s.
    - lcells : the partition of W into left cells
    - duflo  : the corresponding distinguished involutions, together with
      their a-invariants and the sign n_d.
    - lorder : the partial order on left cells (given as an incidence
      matrix)
    - lcells : the partition of W into left cells
    - rcells : the partition of W into right cells
    - tcells : the partition of W into two-sided cells

    As in 'ainvariants', a weight function is given  by  a  sequence  of
    non-negative  integers corresponding to the simple reflections of W,
    where  weights  for simple reflections which are conjugate in W have
    to be equal.  This gives rise to a weight function  L from  W to the
    integers  in  the sense of Lusztig; given w in W, we have

         L(w) = weightL[s_1] + weightL[s_2] + ... + weightL[s_k]

    where w=(s_1, ..., s_k) is a reduced expression for w.  It is  allowed
    that weightL is just an integer, in which case all weights  will  be
    set  equal to that integer.

    >>> W = coxeter("B", 2)
    >>> kl=klpolynomials(W, [2, 1], v)
    >>> kl['klpols']   # negative coefficients do occur!
    [1, 1-v**2, 1+v**2]

    elements are represented by their index in 'elms':

    >>> kl['lcells']
    [[0], [1, 4], [2], [3, 6], [5], [7]]

    >>> [[kl['elms'][w] for w in c] for c in kl['lcells']]
    [[[]],
     [[0], [1, 0]],
     [[1]],
     [[0, 1], [1, 0, 1]],
     [[0, 1, 0]],
     [[0, 1, 0, 1]]]

    >>> kl['elms'][5]
    [0, 1, 0]
    >>> kl['elms'][0]
    []
    >>> kl['klmat'][5][0]
    'c1cc'
    >>> kl['klpols'][int(kl['klmat'][5][0][1])]
    1-v**2

    (Thus, we have P_{[], [0, 1, 0]}=1-v**2.)

    In general, P_{elms[y], elms[w]} is given by

        kl['klpols'][int(kl['klmat'][w][y].split('c')[1])]

    If weightL[s]>0 and sy<y<w<sw, then mu_{elms[y], elms[w]}^s is  given
    by

        kl['mpols'][s][int(kl['klmat'][w][y].split('c')[s+2])]

    >>> kl['duflo']
    [[0, 0, 1], [1, 2, 1], [2, 1, 1], [6, 2, 1], [5, 3, -1], [7, 6, 1]]

    Here, each triple consists of d, a(d), n_d where d is the index of the
    distinguished involution in the list 'elms',  a(d)  is the degree of
    the Kazhdan-Lusztig polynomial  P_{1, d} and  n_d the  coefficient of
    the highest power of v in P_{1, d}. In the course of the computation,
    it is checked if n_d is 1 or -1,  and also if the function w -> a(w)
    reaches its mimumum at exactly one element of a  left cell (which is
    supposed to be the involution d). -- No counter examples are known!

    If one is merely interested in  the partition  of  W into left cells
    (and not in knowing all the Kazhdan-Lusztig polynomials), then it is
    much more efficient to use the function 'klcells'.

    See also 'klcells', 'relklpols' and 'wgraph'.
    """
    if isinstance(weightL, list):
        poids = weightL
    else:
        poids = len(W.rank) * [weightL]
    if all(i == 1 for i in poids):
        uneq = False
    else:
        uneq = True
    ap = allwords(W)
    Lw = [sum([poids[s] for s in w]) for w in ap]
    lw = [len(w) for w in ap]
    a = [W.wordtocoxelm(c) for c in ap]
    inva = [a.index(W.wordtocoxelm(c[::-1])) for c in ap]
    inva1 = [a[c] for c in inva]
    w0 = longestperm(W)
    aw0 = [a.index(tuple([w0[i] for i in p])) for p in a]
    if verbose:
        lprint('#I Initialising (Bruhat-Chevalley order etc.) ')
    lft = [[inva1.index(tuple([s[i] for i in p]))
            for s in W.permgens] for p in inva1]
    mat = [['c0' + len(W.rank) * 'c']]
    for w in range(1, len(a)):
        if verbose and lw[w] > lw[w - 1]:
            lprint('.')
        s = 0
        while lft[w][s] > w:
            s += 1
        b = ['c']
        for y in range(1, w):
            if lw[y] == lw[w]:
                b.append('f')
            elif lw[w] + lw[y] > W.N:
                b.append(mat[aw0[y]][aw0[w]])
            else:
                if (lft[y][s] < y and lft[y][s] <= lft[w][s] and
                    mat[lft[w][s]][lft[y][s]] == 'c') or (lft[y][s] > y and
                                                          y <= lft[w][s] and mat[lft[w][s]][y] == 'c'):
                    b.append('c')
                else:
                    b.append('f')
        b.append('c')
        mat.append(b[:])
    if verbose:
        lprint('\n#I Computing KL polynomials for elements of length:\n')
        lprint('#I        ')
    klpol = [1]
    klstar = [1]
    mues = [[0] for s in W.rank]
    for w in range(1, len(a)):
        if verbose and lw[w] > lw[w - 1]:
            lprint(str(lw[w]) + ' ')
        for y in range(w, -1, -1):
            if mat[w][y][0] == 'c':
                if y == w:
                    h = 1
                elif inva[w] < w or (inva[w] == w and inva[y] > y):
                    h = klpol[int(mat[inva[w]][inva[y]].split('c')[1])]
                else:
                    s = 0
                    while s < len(W.rank) and (lft[y][s] < y or lft[w][s] > w):
                        s += 1
                    if s < len(W.rank):
                        sw = lft[w][s]
                        sy = lft[y][s]
                        if poids[s] == 0:
                            if sy <= sw and mat[sw][sy][0] == 'c':
                                h = klpol[int(mat[sw][sy].split('c')[1])]
                            else:
                                h = 0
                        else:
                            h = klpol[int(mat[w][sy].split('c')[1])]
                    else:
                        iw = inva[w]
                        iy = inva[y]
                        s = 0
                        while s < len(W.rank) and (
                                lft[iy][s] < iy or lft[iw][s] > iw):
                            s += 1
                        if s < len(W.rank):
                            sw = lft[iw][s]
                            sy = lft[iy][s]
                            if poids[s] == 0:
                                if sy <= sw and mat[sw][sy][0] == 'c':
                                    h = klpol[int(mat[sw][sy].split('c')[1])]
                                else:
                                    h = 0
                            else:
                                h = klpol[int(mat[w][inva[sy]].split('c')[1])]
                        else:  # now recursion
                            s = 0
                            while lft[w][s] > w:
                                s += 1
                            if uneq:
                                for t in W.rank:
                                    if lft[w][t] < w and poids[t] < poids[s]:
                                        s = t
                            sw = lft[w][s]
                            sy = lft[y][s]
                            if poids[s] == 0:
                                h = klpol[int(mat[sw][sy].split('c')[1])]
                            else:
                                h = klpol[int(mat[sw][sy].split('c')[1])]
                                if y <= sw and mat[sw][y][0] == 'c':
                                    h += v**(2 * poids[s]) * \
                                        klpol[int(mat[sw][y].split('c')[1])]
                                for z in range(sw - 1, y - 1, -1):
                                    if lft[z][s] < z and mat[z][y][0] == 'c' and mat[sw][z][0] == 'c':
                                        m = mues[s][int(
                                            mat[sw][z].split('c')[s + 2])]
                                        if m != 0:
                                            h -= m * \
                                                v**(Lw[w] - Lw[z]) * \
                                                klpol[int(
                                                    mat[z][y].split('c')[1])]
                if h not in klpol:
                    mat[w][y] += str(len(klpol))
                    klpol.append(h)
                else:
                    mat[w][y] += str(klpol.index(h))
                hstar = v**(Lw[y] - Lw[w]) * h
                if hstar not in klstar:
                    klstar.append(hstar)
                if uneq:   # now mue polynomial
                    for s in W.rank:
                        if poids[s] > 0 and lft[y][s] < y and lft[w][s] > w:
                            if lw[y] + lw[w] > W.N:
                                if (lw[w] - lw[y]) % 2 == 0:
                                    m = -mues[s][int(mat[aw0[y]][aw0[w]].split('c')[s + 2])]
                                else:
                                    m = mues[s][int(
                                        mat[aw0[y]][aw0[w]].split('c')[s + 2])]
                            elif poids[s] == 1:
                                m = zeropart(v**(1 + Lw[y] - Lw[w]) * h)
                            else:
                                m = nonnegpart(v**(poids[s] + Lw[y] - Lw[w]) * h)
                                for z in range(w - 1, y, -1):
                                    if lft[z][s] < z and mat[z][y][0] == 'c' and mat[w][z][0] == 'c':
                                        mp = pospart(
                                            mues[s][int(mat[w][z].split('c')[s + 2])])
                                        if mp != 0:
                                            m -= nonnegpart(mp * v**(Lw[y] - Lw[z]) *
                                                        klpol[int(mat[z][y].split('c')[1])])
                                if m != 0:
                                    m = barpart(m) + m - zeropart(m)
                            if m not in mues[s]:
                                mat[w][y] += 'c' + str(len(mues[s]))
                                mues[s].append(m)
                            else:
                                mat[w][y] += 'c' + str(mues[s].index(m))
                        else:
                            mat[w][y] += 'c'
                else:
                    m = zeropart(v**(1 + Lw[y] - Lw[w]) * h)
                    for s in W.rank:
                        if lft[y][s] < y and lft[w][s] > w:
                            if m not in mues[s]:
                                mat[w][y] += 'c' + str(len(mues[s]))
                                mues[s].append(m)
                            else:
                                mat[w][y] += 'c' + str(mues[s].index(m))
                        else:
                            mat[w][y] += 'c'
    if verbose:
        lprint('\n#I ')
    pp = []
    for w in range(len(a)):
        for s in W.rank:
            if poids[s] == 0 or (lft[w][s] > w and poids[s] > 0):
                pp.append((w, lft[w][s]))
        for y in range(w):
            if mat[w][y][0] == 'c':
                if any(poids[s] > 0 and lft[y][s] < y and lft[w][s] > w and
                       mues[s][int(mat[w][y].split('c')[s + 2])] != 0
                       for s in W.rank):
                    pp.append((w, y))
    if verbose:
        lprint(str(len(pp)) + ' arrows ')
    adelta = []
    ndelta = []
    for w in range(len(a)):
        p = v**(-Lw[w]) * klpol[int(mat[w][0].split('c')[1])]
        if p == 0:
            adelta.append(-1)
            ndelta.append(0)
        else:
            adelta.append(-p.degree)
            ndelta.append(p.coeffs[-1])
    if verbose:
        lprint('>')
    pp0 = [[w] for w in range(len(a))]
    for p in pp:
        pp0[p[0]].append(p[1])
    pp1 = [p[:] for p in pp0]
    for z in pp1:
        for w in z:
            for y in pp0[w]:
                if y not in z:
                    z.append(y)
        z.sort()
    if verbose:
        lprint('>')
    rest = list(range(len(a)))
    lcells = []
    duflo = []
    checks = True
    while rest:
        l = [x for x in pp1[rest[0]] if rest[0] in pp1[x]]
        i0 = 0
        while ndelta[l[i0]] == 0:
            i0 += 1
        d = l[i0]
        for w in l[i0:]:
            if ndelta[w] != 0 and adelta[w] < adelta[d]:
                d = w
        if len([i for i in l if adelta[i] == adelta[d]]) > 1:
            checks = False
        if not (ndelta[d] == 1 or ndelta[d] == -1):
            checks = False
        duflo.append([d, adelta[d], ndelta[d]])
        lcells.append(l)
        for w in l:
            rest.remove(w)
    if verbose:
        lprint(' ' + str(len(lcells)) + ' left cells ')
    lorder = [[d2[0] in pp1[d1[0]] for d2 in duflo] for d1 in duflo]
    for c1 in range(len(lcells)):
        for c2 in range(len(lcells)):
            if c1 != c2 and lorder[c1][c2] and duflo[c1][1] >= duflo[c2][1]:
                checks = False
    if verbose:
        lprint('>')
    rcells = [[inva[w] for w in l] for l in lcells]
    il, ir = [], []
    for w in range(len(a)):
        i = 0
        while w not in lcells[i]:
            i += 1
        il.append(i)
        i = 0
        while w not in rcells[i]:
            i += 1
        ir.append(i)
    rest = list(range(len(a)))
    tcells = []
    while rest:
        t = [rest[0]]
        for w in t:
            for y in rest:
                if y not in t and (il[w] == il[y] or ir[w] == ir[y]):
                    t.append(y)
        t.sort()
        tcells.append(t)
        for w in t:
            rest.remove(w)
    if verbose:
        lprint('> checks are ' + str(checks) + '\n')
    return {'elms': ap, 'klpols': klpol, 'mpols': mues,
            'klmat': mat, 'arrows': pp,
            'lcells': lcells, 'duflo': duflo, 'lorder': lorder,
            'rcells': rcells, 'tcells': tcells, 'klstar': klstar}


def klpoly1(W, weightL, v):
    """returns the left cells in a form which can be used as input to
    the function 'wgraph'.

    See also 'klpolynomials' and 'wgraph'.
    """
    k = klpolynomials(W, weightL, v)
    return [{'elms': [k['elms'][x] for x in c],
             'mpols': k['mpols'], 'klpols': k['klpols'],
             'klmat': [[k['klmat'][c[w]][c[y]] for y in range(w + 1)]
                       for w in range(len(c))]} for c in k['lcells']]


def relmue(lw, ly, p):
    if p == 0:
        return 0
    if isinstance(p, int):
        if lw - ly == 1:
            return p
        return 0
    if p.degree == lw - ly - 1:
        return p.coeffs[-1]
    return 0


def relklpols(W, W1, cell1, weightL, q):
    r"""returns  the matrix of  relative  Kazhdan-Lusztig polynomials  with
    respect to a left cell in a parabolic subgroup, following

      M. Geck, On the induction of Kazhdan--Lusztig cells, Bull. London
               Math. Soc. 35 (2003), 608--614.

    (This version is for equal parameters only.)

    More precisely, let W be a Coxeter group with generating S. Let J be
    a subset of S and W1 be the parabolic subgroup generated by J. Let X
    be the set of minimal left coset representatives of  W1 in W.  For y
    in X and v in W1, we can write uniquely

           C_{yv}' = T_yC_v' + sum_{x, u} p_{xu, yv}^* T_xC_u'

    where the sum  runs over all  x in X and u in W1  such that  x<y and
    u <=_L v (Kazhdan-Lusztig pre-order in W1);  here, p_{xu, yv}^*  is a
    Laurent polynomial  which only involves  strictly negative powers of
    the indeterminate.  There is an algorithm for  computing p_{xu, yv}^*
    by induction, similar to (but technically more complicated than) the
    usual algorithm for computing the  Kazhdan-Lusztig  polynomials. The
    relation to the traditional  Kazhdan-Lusztig polynomials is given by
    the following formula::

                     / P_{u, v}^*                                  if x=y,
       P_{xu, yv}^* =
                     \ p_{xu, yv}^* + sum_w P_{u, w}^* p_{xw, yv}^*  if x<y,

    where the sum runs over all  w in W1  such  that u<w.  The  function
    actually returns the renormalised polynomials

     p_{xu, yv} = v^{L(yv)-L(xu)} p_{xu, yv}^*.

    The details of the recursion are described in Section 4 of

      M. Geck, PyCox - Computing with (finite) Coxeter groups and
         Iwahori-Hecke algebras.  Dedicated to the Memory of Prof.
         H. Pahlings. LMS J. of Comput. Math. 15 (2012), 231--256.

    On the other hand, this algorithm can be run  in a relative setting,
    which just involves the elements in a set of the form X.C,  where  C
    is a fixed left cell of W1  (or, slightly more generally, a union of
    left cells of W1).  By the main result of the above article, the set
    X.C is a union of left cells of W. So this is done in this function:
    it returns  the  matrix of all  p_{xu, yv}^* where  x, y run over  all
    elements of X and u, v run over all elements of W1 which lie in C.

    Here,  C is given by a  dictionary which has at least the components
    'elms', 'klmat', 'mpols'. For example, such a dictionary is returned
    by the  function 'wgraphtoklmat' (see 'wgraph'). The result can then
    be used as input to  'wgraph',  where  it will produce  the  W-graph
    corresponding to the induced cell X.C.

    It is also possible to use  the dictionary  returned by the function
    'klpolynomials' applied to C=W1. Thus,

            relklpols(W, W1, klpolynomials(W1, 1, v), 1, v)

    will return all  relative  Kazhdan-Lusztig  polynomials  p_{xu, yv}^*
    where x, y run over all of X and u, v run over all of W1.

    >>> W = coxeter("A", 3); W1=reflectionsubgroup(W, [0, 1])
    >>> k1=klcells(W1, 1, v); k1[1]
    [wgraph(coxeter('A',2), [1, 1], [[]]),
     wgraph(coxeter('A',2), [1, 1], [[1], [0, 1]]),
     wgraph(coxeter('A',2), [1, 1], [[0], [1, 0]]),
     wgraph(coxeter('A',2), [1, 1], [[0, 1, 0]])]

    (Thus, W1 of type A2 has  4 left cells:  {}, {1, 01}, {0, 10}, {010}.)
    We induce  the first  left cell to  W and  decompose  the associated
    W-graph into its indecomposable components:

    >>> r=relklpols(W, W1, k1[1][0].wgraphtoklmat(), 1, v)
    >>> G=wgraph(W, 1, r, v).decompose(); G
    [wgraph(coxeter('A',3), [1, 1, 1], [[]]),
     wgraph(coxeter('A',3), [1, 1, 1], [[2], [1, 2], [0, 1, 2]])]

    (Thus, the induced graph has 2 components.)

    See also 'klpolynomials', 'klcells', 'wgraph' and 'allrelklpols'.
    """
    if isinstance(weightL, (list, tuple)):
        poids = weightL
    else:
        poids = len(W.rank) * [weightL]
    # uneq = not all(i == 1 for i in poids)
    J = W1.fusions[W.cartanname]['subJ']
    X1w = [W.coxelmtoword(c) for c in redleftcosetreps(W, J)]
    X1 = [W.wordtoperm(w) for w in X1w]
    Lw = [sum([poids[s] for s in w]) for w in X1w]
    lft = []
    for s in W.rank:
        ls = []
        for w in X1:
            sw = tuple([w[i] for i in W.permgens[s]])
            if sw in X1:
                ls.append(X1.index(sw))
            else:
                t = 0
                while tuple([W.permgens[t][i] for i in w]) != sw:
                    t += 1
                ls.append(-t - 1)
        lft.append(ls)
    Lw1 = [sum([poids[J[s]] for s in w]) for w in cell1['elms']]
    p1 = [W1.wordtoperm(w) for w in cell1['elms']]
    lft1 = {}
    for t in W1.rank:
        l = []
        for w in p1:
            w1 = tuple([w[i] for i in W1.permgens[t]])
            if w1 in p1:
                l.append(p1.index(w1))
            else:
                if w[t] >= W1.N:  # tw<w
                    l.append(-1)
                else:           # tw>w
                    l.append(len(p1))
        lft1[J[t]] = l
    bruhatX = []
    for y in range(len(X1)):
        bruhatX.append([bruhatperm(W, X1[x], X1[y], lx=Lw[x], ly=Lw[y])
                        for x in range(y + 1)])
    mat = {}
    mues = [0, 1]
    for y in range(len(X1)):
        for x in range(y):
            if bruhatX[y][x]:
                mat[y, x] = [len(p1) * ['f'] for i in range(len(p1))]
                for v in range(len(p1)):
                    for u in range(len(p1)):
                        if (x == y and u == v) or Lw[x] + Lw1[u] < Lw[y] + Lw1[v]:
                            mat[y, x][v][u] = 'c'
        mat[y, y] = [len(p1) * ['f'] for i in range(len(p1))]
        for i in range(len(p1)):
            for j in range(i):
                if cell1['klmat'][i][j][0] == 'c':
                    mat[y, y][i][j] = 'c0'
                    rk = cell1['klmat'][i][j].split('c')[2:]
                    r = 0
                    while r < len(rk) and (rk[r] == '' or rk[r] == '0'):
                        r += 1
                    if r < len(rk):
                        m = cell1['mpols'][r][int(rk[r])]
                        if m in mues:
                            mat[y, y][i][j] += 'c' + str(mues.index(m))
                        else:
                            mat[y, y][i][j] += 'c' + str(len(mues))
                            mues.append(m)
                    else:
                        mat[y, y][i][j] += 'c0'
            mat[y, y][i][i] = 'c1c0'
    rklpols = [0, 1]
    for y in range(len(X1)):
        # lprint('+')
        ldy = W.leftdescentsetperm(X1[y])
        for x in range(y - 1, -1, -1):
            if bruhatX[y][x]:  # and mat[y, x][0][0][0]=='c':
                fs = [s for s in ldy if lft[s][x] > x]
                fs1 = [s1 for s1 in ldy if 0 <= lft[s1][x] < x]
                if len(fs) > 0:  # case sy<y, sx>x and sx in X
                    s = fs[0]
                    for v in range(len(p1)):
                        for u in range(len(p1)):
                            if mat[y, x][v][u][0] == 'c':
                                if bruhatX[y][lft[s][x]] and mat[y, lft[s][x]][v][u][0] == 'c':
                                    mat[y, x][v][u] += mat[y, lft[s]
                                        [x]][v][u].split('c')[1]
                                    rk = mat[y, x][v][u].split('c')[1]
                                    if rk != '0':
                                        m = relmue(Lw[y] + Lw1[v], Lw[x] +
                                                 Lw1[u], rklpols[int(rk)])
                                        if m in mues:
                                            mat[y, x][v][u] += 'c' + \
                                                str(mues.index(m))
                                        else:
                                            mat[y, x][v][u] += 'c' + str(len(mues))
                                            mues.append(m)
                                    else:
                                        mat[y, x][v][u] += 'c0'
                                else:
                                    mat[y, x][v][u] += '0c0'
                else:
                    for u in range(len(p1)):
                        if any(lft[s1][x] < 0 and u < lft1[-1 - lft[s1][x]][u] for s1 in ldy):
                            for v in range(len(p1)):
                                if mat[y, x][v][u][0] == 'c':
                                    mat[y, x][v][u] += '0c0'
                        else:
                            # fs1=list(filter(lambda s2:lft[s2][x]<0 and
                            #                              lft1[-1-lft[s2][x]][u]<u, ldy))
                            if len(fs1) > 0:
                                s = fs1[0]
                                # lprint('!')
                            else:
                                s = ldy[0]
                            sx, sy = lft[s][x], lft[s][y]
                            for v in range(len(p1)):
                                if mat[y, x][v][u][0] == 'c':
                                    h = 0
                                    for z in range(x, sy):
                                        sz = lft[s][z]
                                        if sz < z and bruhatX[sy][z] and bruhatX[z][x]:
                                            for w in range(len(p1)):
                                                if (sz >= 0 or lft1[-1 - sz][w] < w) and (mat[z, x][w][
                                                        u][0] == 'c' and mat[sy, z][v][w][0] == 'c'):
                                                    m = mues[int(
                                                        mat[sy, z][v][w].split('c')[2])]
                                                    if m != 0:
                                                        rk = mat[z, x][w][u].split('c')[
                                                            1]
                                                        if rk != '0':
                                                            h -= q**(Lw[y] + Lw1[v] - Lw[z] - Lw1[w]) * rklpols[
                                                                int(rk)] * m
                                    if sx < 0:  # case sx not in X, tu<u
                                        t = -1 - sx
                                        if mat[sy, x][v][u][0] == 'c':
                                            rk = mat[sy, x][v][u].split('c')[1]
                                            if rk != '0':
                                                h += (q**2 + 1) * rklpols[int(rk)]
                                        if 0 <= lft1[t][u] < len(p1) and mat[sy, x][v][lft1[t][
                                                u]][0] == 'c':
                                            rk = mat[sy, x][v][lft1[t][u]].split('c')[
                                                1]
                                            if rk != '0':
                                                h += rklpols[int(rk)]
                                        for w in range(u + 1, len(p1)):
                                            if lft1[t][w] > w and (mat[sy, x][v][w][0] == 'c' and
                                                                   cell1['klmat'][w][u][0] == 'c'):
                                                m = mues[int(
                                                    mat[0, 0][w][u].split('c')[2])]
                                                if m != 0:
                                                    rk = mat[sy, x][v][w].split('c')[
                                                        1]
                                                    if rk != '0':
                                                        h += q**(Lw1[w] - Lw1[u] + 1) * \
                                                            rklpols[int(
                                                                rk)] * m
                                    else:    # case sx<x
                                        if mat[sy, sx][v][u][0] == 'c':
                                            rk = mat[sy, sx][v][u].split('c')[1]
                                            if rk != '0':
                                                h += rklpols[int(rk)]
                                        if x <= sy and bruhatX[sy][x] and mat[sy, x][v][u][0] == 'c':
                                            rk = mat[sy, x][v][u].split('c')[1]
                                            if rk != '0':
                                                h += q**2 * rklpols[int(rk)]
                                    if h == 0:
                                        mat[y, x][v][u] += '0c0'
                                    else:
                                        if h in rklpols:
                                            mat[y,
                                                x][v][u] += str(rklpols.index(h))
                                        else:
                                            mat[y, x][v][u] += str(len(rklpols))
                                            rklpols.append(h)
                                        m = relmue(Lw[y] + Lw1[v], Lw[x] + Lw1[u], h)
                                        if m in mues:
                                            mat[y, x][v][u] += 'c' + \
                                                str(mues.index(m))
                                        else:
                                            mat[y, x][v][u] += 'c' + str(len(mues))
                                            mues.append(m)
    # lprint('\n')
    ap = []
    for y in X1w:
        for v in cell1['elms']:
            ap.append(W.reducedword(y + [J[s] for s in v], W))
    ap.sort(key=(lambda x: len(x)))
    ap1 = [W.wordtoperm(w) for w in ap]
    elms1 = [W.wordtoperm([J[s] for s in w1]) for w1 in cell1['elms']]
    bij = {}
    for y in range(len(X1)):
        for v in range(len(elms1)):
            bij[y, v] = ap1.index(permmult(X1[y], elms1[v]))
    nmat = []
    for i in range(len(ap)):
        nmat.append(['f' for j in range(i + 1)])
    for y in range(len(X1)):
        for x in range(y + 1):
            if bruhatX[y][x]:
                for v in range(len(p1)):
                    for u in range(len(p1)):
                        if bij[x, u] <= bij[y, v] and mat[y, x][v][u][0] != 'f':
                            nmat[bij[y, v]][bij[x, u]] = mat[y, x][v][u]
    return {'elms': ap, 'perm': ap1, 'elmsX': X1w, 'rklpols': rklpols,
            'mpols': mues,
            'relklmat': mat, 'klmat': nmat, 'bijection': bij}


def relklpolsuneq(W, W1, cell1, weightL, q):
    """This function implements the same algorithm as 'relklpols' but this
    is the version for unequal parameters  where the computation of the
    mue-polynomials is considerably more involved. For more details see

      M. Geck, PyCox - Computing with (finite) Coxeter groups and
         Iwahori-Hecke algebras.  Dedicated to the Memory of Prof.
         H. Pahlings. LMS J. of Comput. Math. 15 (2012), 231--256.

    See also 'relklpols'.
    """
    if isinstance(weightL, list):
        poids = weightL
    else:
        poids = len(W.rank) * [weightL]
    # uneq = not all(i==1 for i in poids)
    J = W1.fusions[W.cartanname]['subJ']
    X1w = [W.coxelmtoword(c) for c in redleftcosetreps(W, J)]
    X1 = [W.wordtoperm(w) for w in X1w]
    Lw = [sum([poids[s] for s in w]) for w in X1w]
    lft = []
    for s in W.rank:
        ls = []
        for w in X1:
            sw = tuple([w[i] for i in W.permgens[s]])
            if sw in X1:
                ls.append(X1.index(sw))
            else:
                t = 0
                while tuple([W.permgens[t][i] for i in w]) != sw:
                    t += 1
                ls.append(-t - 1)
        lft.append(ls)
    Lw1 = [sum([poids[J[s]] for s in w]) for w in cell1['elms']]
    lw1 = [len(w) for w in cell1['elms']]
    p1 = [W1.wordtoperm(w) for w in cell1['elms']]
    lft1 = {}
    for t in W1.rank:
        l = []
        for w in p1:
            w1 = tuple([w[i] for i in W1.permgens[t]])
            if w1 in p1:
                l.append(p1.index(w1))
            else:
                if w[t] >= W1.N:  # tw<w
                    l.append(-1)
                else:           # tw>w
                    l.append(len(p1))
        lft1[J[t]] = l
    bruhatX = []
    for y in range(len(X1)):
        bruhatX.append([bruhatperm(W, X1[x], X1[y], lx=len(X1w[x]),
                                   ly=len(X1w[y])) for x in range(y + 1)])
    mues = [[0, 1] for s in W.rank]
    rklpols = [0, 1]
    mat = {}
    for y in range(len(X1)):
        for x in range(y):
            if bruhatX[y][x]:
                mat[y, x] = [len(p1) * ['f'] for i in range(len(p1))]
                for v in range(len(p1)):
                    for u in range(len(p1)):
                        if len(X1w[x]) + lw1[u] < len(X1w[y]) + lw1[v]:
                            mat[y, x][v][u] = 'c'
        mat[y, y] = [len(p1) * ['f'] for i in range(len(p1))]
        for i in range(len(p1)):
            mat[y, y][i][i] = 'c1' + len(W.rank) * 'c0'
            for j in range(i):
                if cell1['klmat'][i][j][0] == 'c':
                    mat[y, y][i][j] = 'c0'
                    for s in W.rank:
                        if poids[s] > 0 and lft[s][y] < 0:
                            t = -1 - lft[s][y]
                            if lft1[t][i] > i and lft1[t][j] < j:
                                m = cell1['mpols'][J.index(t)][int(cell1['klmat'][i][
                                    j].split('c')[J.index(t) + 2])]
                                if m in mues[s]:
                                    mat[y, y][i][j] += 'c' + str(mues[s].index(m))
                                else:
                                    mat[y, y][i][j] += 'c' + str(len(mues[s]))
                                    mues[s].append(m)
                            else:
                                mat[y, y][i][j] += 'c0'
                        else:
                            mat[y, y][i][j] += 'c0'
    for y in range(len(X1)):
        # lprint('+')
        ldy = W.leftdescentsetperm(X1[y])
        ldy.sort(key=(lambda p: poids[p]))
        fs0 = [s0 for s0 in ldy if poids[s0] == 0]
        for x in range(y - 1, -1, -1):
            if bruhatX[y][x]:  # and mat[y, x][0][0][0]=='c':
                fs = [s for s in ldy if lft[s][x] > x and poids[s] > 0]
                fs1 = [s1 for s1 in ldy if 0 <= lft[s1][x] < x and poids[s1] > 0]
                if len(fs0) > 0:  # case sy<y and L(s)=0
                    sx, sy = lft[fs0[0]][x], lft[fs0[0]][y]
                    for v in range(len(p1)):
                        for u in range(len(p1)):
                            if mat[y, x][v][u][0] == 'c':
                                if sx >= 0:
                                    if sx <= sy and bruhatX[sy][sx] and mat[sy, sx][v][u][0] == 'c':
                                        mat[y, x][v][u] += mat[sy,
                                            sx][v][u].split('c')[1]
                                    else:
                                        mat[y, x][v][u] += '0'
                                else:
                                    tu = lft1[-1 - sx][u]
                                    if 0 <= tu < len(p1):
                                        if x <= sy and bruhatX[sy][x] and mat[sy, x][v][tu][0] == 'c':
                                            mat[y, x][v][u] += mat[sy,
                                                x][v][tu].split('c')[1]
                                        else:
                                            mat[y, x][v][u] += '0'
                                    else:
                                        mat[y, x][v][u] += '0'
                elif len(fs) > 0:  # case sy<y, sx>x and sx in X
                    s = fs[0]
                    for v in range(len(p1)):
                        for u in range(len(p1)):
                            if mat[y, x][v][u][0] == 'c':
                                if bruhatX[y][lft[s][x]] and mat[y, lft[s][x]][v][u][0] == 'c':
                                    mat[y, x][v][u] += mat[y, lft[s]
                                        [x]][v][u].split('c')[1]
                                else:
                                    mat[y, x][v][u] += '0'
                else:
                    for u in range(len(p1)):
                        if any(lft[s1][x] < 0 and u < lft1[-1 - lft[s1][x]][u] for s1 in ldy):
                            for v in range(len(p1)):
                                if mat[y, x][v][u][0] == 'c':
                                    mat[y, x][v][u] += '0'
                        else:
                            # fs1=list(filter(lambda s2:lft[s2][x]<0 and
                            #                              lft1[-1-lft[s2][x]][u]<u, ldy))
                            if len(fs1) > 0:
                                s = fs1[0]
                                # lprint('!')
                            else:
                                s = ldy[0]
                            sx, sy = lft[s][x], lft[s][y]
                            for v in range(len(p1)):
                                if mat[y, x][v][u][0] == 'c':
                                    h = 0
                                    for z in range(x, sy):
                                        sz = lft[s][z]
                                        if sz < z and bruhatX[sy][z] and bruhatX[z][x]:
                                            for w in range(len(p1)):
                                                if (sz >= 0 or lft1[-1 - sz][w] < w) and (mat[z, x][w][
                                                        u][0] == 'c' and mat[sy, z][v][w][0] == 'c'):
                                                    m = mues[s][int(
                                                        mat[sy, z][v][w].split('c')[s + 2])]
                                                    if m != 0:
                                                        rk = mat[z, x][w][u].split('c')[1]
                                                        if rk != '0':
                                                            h -= q**(Lw[y] + Lw1[v] - Lw[z] - Lw1[w]) * rklpols[
                                                                int(rk)] * m
                                    if sx < 0:  # case sx not in X, tu<u
                                        t = -1 - sx
                                        if mat[sy, x][v][u][0] == 'c':
                                            rk = mat[sy, x][v][u].split('c')[1]
                                            if rk != '0':
                                                h += (q**(2 * poids[s]) + 1) * \
                                                    rklpols[int(rk)]
                                        if 0 <= lft1[t][u] < len(p1) and mat[sy, x][v][lft1[t][
                                                u]][0] == 'c':
                                            rk = mat[sy, x][v][lft1[t][u]].split('c')[
                                                1]
                                            if rk != '0':
                                                h += rklpols[int(rk)]
                                        for w in range(u + 1, len(p1)):
                                            if lft1[t][w] > w and (mat[sy, x][v][w][0] == 'c' and
                                                                   cell1['klmat'][w][u][0] == 'c'):
                                                m1 = cell1['mpols'][J.index(t)][int(cell1['klmat'][
                                                    w][u].split('c')[J.index(t) + 2])]
                                                if m1 != 0:
                                                    rk = mat[sy, x][v][w].split('c')[1]
                                                    if rk != '0':
                                                        h += q**(Lw1[w] - Lw1[u] + poids[t]
                                                                 ) * rklpols[int(rk)] * m1
                                    else:    # case sx<x
                                        if mat[sy, sx][v][u][0] == 'c':
                                            rk = mat[sy, sx][v][u].split('c')[1]
                                            if rk != '0':
                                                h += rklpols[int(rk)]
                                        if x <= sy and bruhatX[sy][x] and mat[sy, x][v][u][0] == 'c':
                                            rk = mat[sy, x][v][u].split('c')[1]
                                            if rk != '0':
                                                h += q**(2 * poids[s]) * rklpols[int(rk)]
                                    if h == 0:
                                        mat[y, x][v][u] += '0'
                                    else:
                                        if h in rklpols:
                                            mat[y,
                                                x][v][u] += str(rklpols.index(h))
                                        else:
                                            mat[y, x][v][u] += str(len(rklpols))
                                            rklpols.append(h)
                for v in range(len(p1)):
                    for u in range(len(p1)):
                        if mat[y, x][v][u][0] == 'c':
                            for r in W.rank:
                                if poids[r] > 0 and (lft[r][y] > y or (lft[r][y] < 0 and
                                        v < lft1[-1 - lft[r][y]][v])) and (0 <= lft[r][x] < x or
                                               (lft[r][x] < 0 and lft1[-1 - lft[r][x]][u] < u)):
                                    if poids[r] == 1:
                                        m = relmue(Lw[y] + Lw1[v], Lw[x] + Lw1[u],
                                             rklpols[int(mat[y, x][v][u].split('c')[1])])
                                    else:
                                        pis = 0
                                        for z in range(x + 1, y + 1):
                                            if bruhatX[z][x] and bruhatX[y][z]:
                                                for w in range(len(p1)):
                                                    if 0 <= lft[r][z] < z or (lft[r][z] < 0 and
                                                                           lft1[-1 - lft[r][z]][w] < w):
                                                        if mat[z, x][w][u][0] == 'c' and mat[y,
                                                                                     z][v][w][0] == 'c':
                                                            m1 = pospart(mues[r][int(mat[y, z][v][
                                                                w].split('c')[r + 2])])
                                                            if m1 != 0:
                                                                pis += nonnegpart(q**(Lw1[u] + Lw[x] - Lw1[w] -
                                                                          Lw[z]) * rklpols[int(mat[z, x][w][
                                                                              u].split('c')[1])] * m1)
                                        rk = mat[y, x][v][u].split('c')[1]
                                        if rk != '0':
                                            pis -= nonnegpart(q**(Lw1[u] + Lw[x] - Lw1[v] - Lw[y] +
                                                                  poids[r]) * rklpols[int(rk)])
                                        if lft[r][x] < 0:
                                            t = -1 - lft[r][x]
                                        # if lft1[t][u]>=0 and mat[y, x][v][lft1[t][u]][0]=='c':
                                        #  rk=mat[y, x][v][lft1[t][u]].split('c')[1]
                                        #  if rk!='0':
                                        #    pis-=nonnegpart(q**(Lw1[u]+Lw[x]-Lw1[v]-Lw[y]-
                                        #                           poids[t])*rklpols[int(rk)])
                                            for w in range(u + 1, len(p1)):
                                                if w < lft1[t][w] and cell1['klmat'][w][u][0] == 'c':
                                                    m1 = pospart(cell1['mpols'][J.index(t)][int(cell1[
                                                        'klmat'][w][u].split('c')[J.index(t) + 2])])
                                                    if m1 != 0 and mat[y, x][v][w][0] == 'c':
                                                        rk = mat[y, x][v][w].split('c')[
                                                            1]
                                                        if rk != '0':
                                                            pis -= nonnegpart(rklpols[int(rk)] *
                                                                    q**(Lw1[w] + Lw[x] - Lw1[v] - Lw[y]) * m1)
                                        if pis != 0:
                                            pis = barpart(pis) + pis - zeropart(pis)
                                        m = -pis
                                    # if all(p==1 for p in poids):
                                    #  m1=relmue(Lw[y]+Lw1[v], Lw[x]+Lw1[u],
                                    #       rklpols[int(mat[y, x][v][u].split('c')[1])])
                                    #  if m!=m1:
                                    #    print("mist!")
                                    #    print([m, m1])
                                    #    return [m, m1]
                                    if m in mues[r]:
                                        mat[y, x][v][u] += 'c' + \
                                            str(mues[r].index(m))
                                    else:
                                        mat[y, x][v][u] += 'c' + str(len(mues[r]))
                                        mues[r].append(m)
                                else:
                                    mat[y, x][v][u] += 'c0'
    ap = []
    for y in X1w:
        for v in cell1['elms']:
            ap.append(W.reducedword(y + [J[s] for s in v], W))
    ap.sort(key=(lambda x: len(x)))
    ap1 = [W.wordtoperm(w) for w in ap]
    elms1 = [W.wordtoperm([J[s] for s in w1]) for w1 in cell1['elms']]
    bij = {}
    for y in range(len(X1)):
        for v in range(len(elms1)):
            bij[y, v] = ap1.index(permmult(X1[y], elms1[v]))
    nmat = []
    for i in range(len(ap)):
        nmat.append(['f' for j in range(i + 1)])
    for y in range(len(X1)):
        for x in range(y + 1):
            if bruhatX[y][x]:
                for v in range(len(p1)):
                    for u in range(len(p1)):
                        if bij[x, u] <= bij[y, v] and mat[y, x][v][u][0] != 'f':
                            nmat[bij[y, v]][bij[x, u]] = mat[y, x][v][u]
    return {'elms': ap, 'perm': ap1, 'elmsX': X1w, 'rklpols': rklpols,
            'mpols': mues,
            'relklmat': mat, 'klmat': nmat, 'bijection': bij}


def allrelklpols(W, J, weightL, q, verbose=False):
    r"""returns the matrix of all  relative Kazhdan-Lusztig polynomials with
    respect to a parabolic subgroup, following

      M. Geck, On the induction of Kazhdan--Lusztig cells, Bull. London
               Math. Soc. 35 (2003), 608--614.

    (For the time being, it is only implemented for equal parameters.)

    More precisely, let W be a Coxeter group with generating S. Let J be
    a subset of S and X be the set of minimal left coset representatives
    of W_J in W. For y in X and v in W_J, we can write uniquely

           C_{yv}' = T_yC_v' + sum_{x, u} p_{xu, yv}^* T_xC_u'

    where the sum  runs over all  x in X and u in W_J such that  x<y and
    u <=_L v (Kazhdan-Lusztig pre-order in W_J);  here, p_{xu, yv}^* is a
    Laurent polynomial  which only involves  strictly negative powers of
    the indeterminate.  There is an algorithm for  computing p_{xu, yv}^*
    by induction, similar to (but technically more complicated than) the
    usual  algorithm for computing the  Kazhdan-Lusztig polynomials. The
    relation to the traditional  Kazhdan-Lusztig polynomials is given by
    the following formula::

                     / P_{u, v}^*                                  if x=y,
       P_{xu, yv}^* =
                     \ p_{xu, yv}^* + sum_w P_{u, w}^* p_{xw, yv}^*  if x<y,

    where the sum runs over all  w in W_J  such  that u<w.  The function
    actually returns the renormalised polynomials

     p_{xu, yv} = v^{L(yv)-L(xu)} p_{xu, yv}^*.

    >>> W = coxeter("B", 2)
    >>> relklpols(W, [0], 1, v)
    {'allelms':  [[], [0], [1], [0, 1], [1, 0], [0, 1, 0], [1, 0, 1], [0, 1, 0, 1]],
     'elmsX':    [[], [1], [0, 1], [1, 0, 1]],
     'elmsJ':    [[], [0]],
     'klpols':   [1],
     'rklpols':  [0, 1],
     'mues':     [0, 1],
     'relklmat': {(0, 0): [['c1c0', 'f'   ], ['c0c1', 'c1c0']],
                  (1, 0): [['c1c1', 'f'   ], ['c0c0', 'c1c1']],
                  (1, 1): [['c1c0', 'f'   ], ['c0c1', 'c1c0']],
                  (2, 0): [['c0c0', 'c1c1'], ['c0c0', 'c1c0']],
                  (2, 1): [['c1c1', 'f'   ], ['c0c0', 'c1c1']],
                  (2, 2): [['c1c0', 'f'   ], ['c0c1', 'c1c0']],
                  (3, 0): [['c0c0', 'c1c0'], ['c0c0', 'c1c0']],
                  (3, 1): [['c0c0', 'c1c1'], ['c0c0', 'c1c0']],
                  (3, 2): [['c1c1', 'f'   ], ['c0c0', 'c1c1']],
                  (3, 3): [['c1c0', 'f'   ], ['c0c1', 'c1c0']],
      'arrows':  [(0, 1), (0, 2), (1, 4), (2, 3), (4, 5), (4, 1), (3, 6), (3, 2),
                  (5, 7), (5, 4), (6, 7), (6, 3)]}

    (Conventions in relklmat similar to those in 'klpolynomials'.

    See also 'klpolynomials' and 'klcells'.
    """
    if isinstance(weightL, list):
        poids = weightL
    else:
        poids = len(W.rank) * [weightL]
    # uneq = not all(i == 1 for i in poids)
    ap = allwords(W)
    W1 = reflectionsubgroup(W, J)
    m1 = klpolynomials(W1, [poids[s] for s in J], q)
    wa1 = [[J[s] for s in c] for c in m1['elms']]
    a1 = [W.wordtoperm(w) for w in wa1]
    X1 = [W.coxelmtoperm(c) for c in redleftcosetreps(W, J)]
    Lw1 = [sum([poids[s] for s in w]) for w in wa1]
    X1w = [W.permtoword(p) for p in X1]
    Lw = [sum([poids[s] for s in w]) for w in X1w]
    lft = []
    for s in W.rank:
        ls = []
        for w in X1:
            sw = tuple([w[i] for i in W.permgens[s]])
            if sw in X1:
                ls.append(X1.index(sw))
            else:
                t = 0
                while tuple([W.permgens[t][i] for i in w]) != sw:
                    t += 1
                ls.append(-t - 1)
        lft.append(ls)
    lft1 = {}
    for t in J:
        lft1[t] = [a1.index(tuple([w[i] for i in W.permgens[t]])) for w in a1]
    mat = {}
    if verbose:
        lprint('#I Initialising ')
    mues = [0]
    for y in range(len(X1)):
        if verbose and y % 100 == 0:
            lprint('.')
        for x in range(y):
            if bruhatperm(W, X1[x], X1[y]):
                # if x==y or Lw[x]<Lw[y]:
                mat[y, x] = [len(a1) * ['f'] for i in range(len(a1))]
                for v in range(len(a1)):
                    for u in range(len(a1)):
                        #         if bruhatperm(W, permmult(X1[x], a1[u]), permmult(X1[y], a1[v])):
                        if (x == y and u == v) or Lw[x] + Lw1[u] < Lw[y] + Lw1[v]:
                            mat[y, x][v][u] = 'c'
            else:
                mat[y, x] = [len(a1) * ['f'] for i in range(len(a1))]
        mat[y, y] = [len(a1) * ['f'] for i in range(len(a1))]
        for i in range(len(a1)):
            for j in range(i):
                if m1['klmat'][i][j][0] == 'c':
                    mat[y, y][i][j] = 'c0'
                    m = relmue(Lw1[i], Lw1[j],
                               m1['klpols'][int(m1['klmat'][i][j].split('c')[1])])
                    if m in mues:
                        mat[y, y][i][j] += 'c' + str(mues.index(m))
                    else:
                        mat[y, y][i][j] += 'c' + str(len(mues))
                        mues.append(m)
            mat[y, y][i][i] = 'c1c0'
    if verbose:
        lprint('\n#I ')
    rklpols = [0, 1]
    for y in range(len(X1)):
        if verbose:
            lprint('+')
        ldy = W.leftdescentsetperm(X1[y])
        for x in range(y - 1, -1, -1):
            if mat[y, x][0][0][0] == 'c':
                fs = [s for s in ldy if lft[s][x] > x]
                fs1 = [s1 for s1 in ldy if 0 <= lft[s1][x] < x]
                if len(fs) > 0:  # case sy<y, sx>x and sx in X
                    s = fs[0]
                    for v in range(len(a1)):
                        for u in range(len(a1)):
                            if mat[y, x][v][u][0] == 'c':
                                if mat[y, lft[s][x]][v][u][0] == 'c':
                                    mat[y, x][v][u] += mat[y, lft[s]
                                        [x]][v][u].split('c')[1]
                                    rk = mat[y, x][v][u].split('c')[1]
                                    if rk != '0':
                                        m = relmue(Lw[y] + Lw1[v], Lw[x] +
                                                 Lw1[u], rklpols[int(rk)])
                                        if m in mues:
                                            mat[y, x][v][u] += 'c' + \
                                                str(mues.index(m))
                                        else:
                                            mat[y, x][v][u] += 'c' + str(len(mues))
                                            mues.append(m)
                                    else:
                                        mat[y, x][v][u] += 'c0'
                                else:
                                    mat[y, x][v][u] += '0c0'
                else:
                    for u in range(len(a1)):
                        if any(lft[s1][x] < 0 and lft1[-1 - lft[s1][x]][u] > u for s1 in ldy):
                            for v in range(len(a1)):
                                if mat[y, x][v][u][0] == 'c':
                                    mat[y, x][v][u] += '0c0'
                        else:
                            # fs1=list(filter(lambda s2:lft[s2][x]<0 and
                            #                              lft1[-1-lft[s2][x]][u]<u, ldy))
                            if len(fs1) > 0:
                                s = fs1[0]
                            else:
                                s = ldy[0]
                            sx, sy = lft[s][x], lft[s][y]
                            for v in range(len(a1)):
                                if mat[y, x][v][u][0] == 'c':
                                    h = 0
                                    for z in range(x, sy):
                                        if lft[s][z] < z:
                                            for w in range(len(a1)):
                                                if (lft[s][z] >= 0 or lft1[-1 - lft[s][z]][w] < w) and (
                                                   mat[z, x][w][u][0] == 'c' and mat[sy, z][v][w][0] == 'c'):
                                                    m = mues[int(
                                                        mat[sy, z][v][w].split('c')[2])]
                                                    if m != 0:
                                                        rk = mat[z, x][w][u].split('c')[
                                                            1]
                                                        if rk != '0':
                                                            h -= q**(Lw[y] + Lw1[v] - Lw[z] - Lw1[w]) * rklpols[
                                                                int(rk)] * m
                                    if sx < 0:  # case sx not in X, tu<u
                                        t = -1 - sx
                                        if mat[sy, x][v][u][0] == 'c':
                                            rk = mat[sy, x][v][u].split('c')[1]
                                            if rk != '0':
                                                h += (q**2 + 1) * rklpols[int(rk)]
                                        if mat[sy, x][v][lft1[t][u]][0] == 'c':
                                            rk = mat[sy, x][v][lft1[t][u]].split('c')[
                                                1]
                                            if rk != '0':
                                                h += rklpols[int(rk)]
                                        for w in range(u + 1, len(a1)):
                                            if lft1[t][w] > w and (mat[sy, x][v][w][0] == 'c' and
                                                                   m1['klmat'][w][u][0] == 'c'):
                                                m = mues[int(
                                                    mat[0, 0][w][u].split('c')[2])]
                                                if m != 0:
                                                    rk = mat[sy, x][v][w].split('c')[
                                                        1]
                                                    if rk != '0':
                                                        h += q**(Lw1[w] - Lw1[u] + 1) * \
                                                            rklpols[int(
                                                                rk)] * m
                                    else:    # case sx<x
                                        if mat[sy, sx][v][u][0] == 'c':
                                            rk = mat[sy, sx][v][u].split('c')[1]
                                            if rk != '0':
                                                h += rklpols[int(rk)]
                                        if x <= sy and mat[sy, x][v][u][0] == 'c':
                                            rk = mat[sy, x][v][u].split('c')[1]
                                            if rk != '0':
                                                h += q**2 * rklpols[int(rk)]
                                    if h == 0:
                                        mat[y, x][v][u] += '0c0'
                                    else:
                                        if h in rklpols:
                                            mat[y,
                                                x][v][u] += str(rklpols.index(h))
                                        else:
                                            mat[y, x][v][u] += str(len(rklpols))
                                            rklpols.append(h)
                                        m = relmue(Lw[y] + Lw1[v], Lw[x] + Lw1[u], h)
                                        if m in mues:
                                            mat[y, x][v][u] += 'c' + \
                                                str(mues.index(m))
                                        else:
                                            mat[y, x][v][u] += 'c' + str(len(mues))
                                            mues.append(m)
    if verbose:
        lprint('\n#I ')
    ap1 = [W.wordtoperm(w) for w in ap]
    bij = {}
    for y in range(len(X1)):
        for v in range(len(a1)):
            bij[y, v] = ap1.index(permmult(X1[y], a1[v]))
    pp = []
    for y in range(len(X1)):
        for v in range(len(a1)):
            for s in W.rank:
                if lft[s][y] > y:
                    pp.append((bij[y, v], bij[lft[s][y], v]))
                elif lft[s][y] < 0 and lft1[-1 - lft[s][y]][v] > v:
                    pp.append((bij[y, v], bij[y, lft1[-1 - lft[s][y]][v]]))
            for x in range(y + 1):
                for u in range(len(a1)):
                    rk = mat[y, x][v][u]
                    if rk[0] == 'c' and rk.split('c')[2] != '0':
                        if any((0 <= lft[s][x] < x or (lft[s][x] < 0 and
                            lft1[-1 - lft[s][x]][u] < u)) and (lft[s][y] > y or (lft[s][y] < 0
                                           and lft1[-1 - lft[s][y]][v] > v)) for s in W.rank):
                            pp.append((bij[y, v], bij[x, u]))
    if verbose:
        lprint(str(len(pp)) + ' arrows \n')
    klpols = []
    for y in range(len(X1)):
        for x in range(y + 1):
            for v in range(len(a1)):
                for u in range(len(a1)):
                    if x == y and u <= v and m1['klmat'][v][u][0] == 'c':
                        h = m1['klpols'][int(m1['klmat'][v][u].split('c')[1])]
                    else:
                        rk = mat[y, x][v][u]
                        if rk[0] == 'c':
                            h = rklpols[int(rk.split('c')[1])]
                            for w in range(u + 1, len(a1)):
                                rk1 = m1['klmat'][w][u]
                                if rk1[0] == 'c':
                                    rk2 = mat[y, x][v][w]
                                    if rk2[0] == 'c' and rk2[1] != '0':
                                        h += m1['klpols'][int(rk1.split('c')[1])] * rklpols[
                                            int(rk2.split('c')[1])]
                    if h != 0 and h not in klpols:
                        klpols.append(h)
    return {'allelms': ap, 'elmsJ': wa1, 'elmsX': X1w, 'rklpols': rklpols,
            'mues': mues, 'relklmat': mat, 'klpols': klpols, 'arrows': pp}


# F leftconnected
def leftconnected(W, elms, verbose=False):
    """returns the  left-connected components of a set elms. A set elms
    if left-connected  if for any two elements x, y in elms, there is
    a sequence  s_1, ..., s_n in S such that  y=s_n...s_2s_1x  and all
    intermediate elements  s_i...s_2s_1x for i=1, ..., n-1 also lie in
    elms. Otherwise, elms falls into left-connected components under
    this relation. It is expected (Lusztig, 1983) that

       * left cells of W are left-connected, and
       * the left-connected components of a two-sided cell are
         precisely the left cells in that two-sided cell.

    """
    if isinstance(elms[0], tuple):  # type of W.permgens
        if len(elms[0]) == 2 * W.N:
            pelms = set([w[:len(W.rank)] for w in elms])
        else:
            pelms = set(elms)
    else:
        pelms = set(W.wordtocoxelm(w) for w in elms)
    orbs = []
    while pelms:
        w1 = next(iter(pelms))
        orb = [W.coxelmtoperm(w1)]
        orb1 = set([w1])
        for x in orb:
            for s in W.rank:
                sx = permmult(W.permgens[s], x)
                if sx[:len(W.rank)] in pelms and (not sx[:len(W.rank)] in orb1):
                    orb.append(sx)
                    orb1.add(sx[:len(W.rank)])
        orbs.append(orb)
        for x in orb:
            pelms.remove(x[:len(W.rank)])
    if verbose:
        lprint('#I ' + str(len(orbs)) + ' left-connected components\n')
    return orbs


# F klstaroperation
def klstaroperation(W, s, t, pcell):
    """returns the list containing the elements  w^* for w in cell, where
    w^* is obtained by the Kazhdan-Lusztig star operation with respect
    to  the generators  s, t in S such that  st has order 3. Here, cell
    is assumed to be a  list of elements in  W which all have the same
    right descent set (and which are given as full permutations).  The
    function  returns  'False'  if the  star operation with respect to
    s, t is not defined for the  elements  in the given set.

    >>> W = coxeter("D", 4); W.coxetermat
    [[1, 2, 3, 2], [2, 1, 3, 2], [3, 3, 1, 3], [2, 2, 3, 1]]

    example of a left cell:

    >>> k=klcells(W, 1, v);cell=k[0][2];cell
    [[3], [2, 3], [0, 2, 3], [1, 2, 3]]
    >>> klstaroperation(W, 0, 2, [W.wordtoperm(p) for p in cell]);
    False
    >>> klstaroperation(W, 1, 2, [W.wordtoperm(p) for p in cell])
    False
    >>> st=klstaroperation(W, 2, 3, [W.wordtoperm(p) for p in cell])
    >>> st is False
    False
    >>> [W.permtoword(p) for p in st]
    [[3, 2], [2], [0, 2], [1, 2]]

    See also 'klstarorbit' and 'wgraphstarorbit'.
    """
    pw1 = perminverse(pcell[0])
    if (pw1[s] >= W.N and pw1[t] >= W.N) or (pw1[s] < W.N and pw1[t] < W.N):
        return False
    nl = []
    for pw in pcell:
        ws = tuple([W.permgens[s][r] for r in pw])
        wsi = perminverse(ws)
        if (wsi[s] >= W.N and wsi[t] < W.N) or (wsi[t] >= W.N and wsi[s] < W.N):
            nl.append(ws)
        else:
            nl.append(tuple([W.permgens[t][r] for r in pw]))
    return nl

# F klstarorbit


def klstarorbit(W, l, gens='each'):
    """returns the orbit of a list 'l'  of elements  under repeated
    application of star operations. Here, it is assumed that all
    elements in 'l' have the same generalised tau-invariant. For
    example, 'l' could be a left cell (equal parameter case)  or
    'l' could be a singleton set.  The optional argument  'gens'
    can be  used to specify  the generators  for which the  star
    operation will be considered.

    >>> W = coxeter("A", 3);k=klcells(W, 1, v)
    >>> cell = k[1][3]; cell
    wgraph(coxeter('A',3), [1, 1, 1], [[2], [1, 2], [0, 1, 2]])
    >>> klstarorbit(W, cell.X)
    [[[2], [1, 2], [0, 1, 2]],
     [[2, 1], [1], [0, 1]],
     [[2, 1, 0], [1, 0], [0]]]

    See  also  'klstaroperation', 'klstarorbitperm', 'klcells' and
    'gentaucells'.
    """
    if gens == 'each':
        gens = list(W.rank)
    # orb = [[W.wordtoperm(x) for x in l]]
    if len(l) == 0 or (isinstance(l[0], tuple) and len(l[0]) == 2 * W.N):
        orb = [l[:]]
    else:
        orb = [[W.wordtoperm(x) for x in l]]
    orb1 = [set([x[:len(W.rank)] for x in orb[0]])]
    for cell in orb:
        for s in range(len(gens)):
            for t in range(s):
                if W.coxetermat[gens[s]][gens[t]] == 3:
                    nc = klstaroperation(W, gens[s], gens[t], cell)
                    if nc is not False and not any(nc[0][:len(W.rank)] in o for o in orb1):
                        orb.append(nc)
                        orb1.append(set([x[:len(W.rank)] for x in nc]))
    return [[W.permtoword(p) for p in o] for o in orb]

# F klstarorbitperm


def klstarorbitperm(W, l, gens='each'):
    """same as klstarorbit but the function returns the elements as
    full permutations.
    """
    if gens == 'each':
        gens = list(W.rank)
    # orb=[[W.wordtoperm(x) for x in l]]
    if len(l) == 0 or (isinstance(l[0], tuple) and len(l[0]) == 2 * W.N):
        orb = [l[:]]
    else:
        orb = [[W.wordtoperm(x) for x in l]]
    orb1 = [set([x[:len(W.rank)] for x in orb[0]])]
    for cell in orb:
        for s in range(len(gens)):
            for t in range(s):
                if W.coxetermat[gens[s]][gens[t]] == 3:
                    nc = klstaroperation(W, gens[s], gens[t], cell)
                    if nc is not False and not any(nc[0][:len(W.rank)] in o for o in orb1):
                        orb.append(nc)
                        orb1.append(set([x[:len(W.rank)] for x in nc]))
    return orb


def klstarorbitchain(W, l, gens='each'):
    """same as 'klstarorbit' but only returns sequence of pairs of
    generators.
    """
    if gens == 'each':
        gens = list(W.rank)
    orb = [[W.wordtoperm(x) for x in l]]
    ch = []
    for cell in orb:
        c1 = []
        for s in range(len(gens)):
            for t in range(s):
                if W.coxetermat[gens[s]][gens[t]] == 3:
                    nc = klstaroperation(W, gens[s], gens[t], cell)
                    if nc is not False and not any(nc[0] in c for c in orb):
                        orb.append(nc)
                        c1.append(str(s) + str(t))
        ch.append(c1)
    return ch

# F leftklstar


def leftklstar(W, pw, s, t):
    """applies the left star operation with respect to generators
    s and t to an element pw; here, it is already assumed that
    the product st has order 3 and that the star  operation is
    known to apply to pw.

    See also 'leftklstarorbit'.
    """
    if pw[s] >= W.N and pw[t] < W.N:
        sw = tuple([pw[i] for i in W.permgens[s]])
        if sw[t] >= W.N:
            return sw
        else:
            return tuple([pw[i] for i in W.permgens[t]])
    else:
        sw = tuple([pw[i] for i in W.permgens[t]])
        if sw[s] >= W.N:
            return sw
        else:
            return tuple([pw[i] for i in W.permgens[s]])

# F leftklstarorbitelm


def leftklstarorbitelm(W, pw, gens='each'):
    """returns the orbit of an element under the left star operations.
    The element  is supposed to  be given as a  full permutation of
    the set of roots (see 'coxeter').

    See also 'leftklstar' and 'leftklstarorbits'.
    """
    if gens == 'each':
        gens = list(W.rank)
    orb = [pw]
    orb1 = set([pw[:len(W.rank)]])
    for d in orb:
        for i in range(len(gens)):
            for j in range(i):
                s, t = gens[i], gens[j]
                if W.coxetermat[s][t] == 3:
                    if (d[s] >= W.N and d[t] < W.N) or (d[s] < W.N and d[t] >= W.N):
                        d1 = leftklstar(W, d, s, t)
                        if d1[:len(W.rank)] not in orb1:
                            orb.append(d1)
                            orb1.add(d1[:len(W.rank)])
    return orb

# F leftklstarorbitelm1


def leftklstarorbitelm1(W, pw, gens='each'):
    """similar to 'leftklstarorbitelm' but takes into account any
    pair s, t of generators such that st has order 3 or 4.
    """
    if gens == 'each':
        gens = list(W.rank)
    orb = [pw]
    orb1 = set([pw[:len(W.rank)]])
    for d in orb:
        for i in range(len(gens)):
            for j in range(len(gens)):
                s, t = gens[i], gens[j]
                if (s < t and W.coxetermat[s][t] == 3) or W.coxetermat[s][t] >= 4:
                    if (d[s] >= W.N and d[t] < W.N) or (d[s] < W.N and d[t] >= W.N):
                        d1 = leftklstar(W, d, s, t)
                        if d1[:len(W.rank)] not in orb1:
                            orb.append(d1)
                            orb1.add(d1[:len(W.rank)])
    return orb

# F klstarorbitelm


def klstarorbitelm(W, pw, gens='each'):
    """returns the orbit of an element under the (right) star operations.

    See also 'leftklstarorbitelm' and 'klstarorbit'.
    """
    return [perminverse(x) for x in leftklstarorbitelm(W, perminverse(pw), gens)]


# F leftklstarorbits
def leftklstarorbits(W, l, lcells=False, gens='each'):
    """returns the orbits of a set under the left star operations.
    If the given set 'l'  is known to be a union of left cells,
    the function performs  faster when  the additional argument
    'lcells' is set to 'True'.

    See also 'leftklstarorbitelm'.
    """
    if gens == 'each':
        gens = list(W.rank)
    orbs = []
    rest = [x for x in l]
    while rest:
        if not lcells:
            o = [x for x in leftklstarorbitelm(W, rest[0], gens) if x in l]
        else:
            o = leftklstarorbitelm(W, rest[0], gens)
        orbs.append(o)
        for w in o:
            rest.remove(w)
    return orbs

# F leftklstarreps


def leftklstarreps(W, l, distinv=[], gens='each'):
    """returns a set of representatives for the orbits of a set under
    the left star operations.

    See also 'leftklstarorbitelm'.
    """
    if gens == 'each':
        gens = list(W.rank)
    reps = []
    rest = [x for x in l]
    while rest != []:
        o = leftklstarorbitelm(W, rest[0], gens)
        o1 = 0
        if distinv != []:
            i = 0
            while o1 == 0 and i < len(o):
                if o[i][:len(W.rank)] in distinv:
                    o1 = o[i]
                else:
                    i += 1
        if o1 == 0:
            i = 0
            while o1 == 0 and i < len(o):
                if W.permorder(o[i]) <= 2:
                    o1 = o[i]
                else:
                    i += 1
        if o1 == 0:
            lno = [W.permlength(w) for w in o]
            reps.append(o[lno.index(min(lno))])
        else:
            reps.append(o1)
        for w in o:
            rest.remove(w)
    return reps

# F leftrightstarorbit


def leftrightstarorbit(W, pw, verbose=False):
    """returns the orbit of an element under repeated applications of
    left or right star operations.
    """
    orb = [pw]
    orb1 = set([pw[:len(W.rank)]])
    for d in orb:
        for s in W.rank:
            for t in range(s):
                if W.coxetermat[s][t] == 3:
                    if (d[s] >= W.N and d[t] < W.N) or (d[s] < W.N and d[t] >= W.N):
                        d1 = leftklstar(W, d, s, t)
                        if not d1[:len(W.rank)] in orb1:
                            orb.append(d1)
                            orb1.add(d1[:len(W.rank)])
                    nc = klstaroperation(W, s, t, [d])
                    if nc is not False and not nc[0][:len(W.rank)] in orb1:
                        orb.append(nc[0])
                        orb1.add(nc[0][:len(W.rank)])
    if verbose:
        lprint('#I orbit of length ' + str(len(orb)) + '\n')
    return orb


def leftrightstarorbitinv(W, pw, verbose=False):
    """similar to 'leftrightstarorbit' but the computation terminates when
    an involution  is  found in the orbit.  In this case,  the function
    returns this involution; otherwise, the whole orbit is returned.
    """
    orb = [pw]
    orb1 = set([pw[:len(W.rank)]])
    for d in orb:
        for s in W.rank:
            for t in range(s):
                if W.coxetermat[s][t] == 3:
                    if (d[s] >= W.N and d[t] < W.N) or (d[s] < W.N and d[t] >= W.N):
                        d1 = leftklstar(W, d, s, t)
                        if not d1[:len(W.rank)] in orb1:
                            if W.permorder(d1) <= 2:
                                if verbose:
                                    lprint('#I found involution\n')
                                return d1
                            orb.append(d1)
                            orb1.add(d1[:len(W.rank)])
                    nc = klstaroperation(W, s, t, [d])
                    if nc is not False and not nc[0][:len(W.rank)] in orb1:
                        if W.permorder(nc[0]) <= 2:
                            if verbose:
                                lprint('#I found involution\n')
                            return nc[0]
                        orb.append(nc[0])
                        orb1.add(nc[0][:len(W.rank)])
    if verbose:
        lprint('#I orbit of length ' + str(len(orb)) + '\n')
    return orb

# F generalisedtau


def generalisedtau(W, pw, maxd=10):
    """returns Vogan's generalised  tau-invariant of an element of
    a finite Coxeter group. It is known that two elements which
    belong to the same left cell  (in the equal parameter case)
    must have the same generalised tau-invariant.  The optional
    argument  'maxd' can be used to set the depth to  which the
    star operations will be applied (default 10).
    """
    # pw=W.wordtoperm(w)
    orb = [pw]
    o = 0
    while o < len(orb) <= maxd:
        for s in W.rank:
            for t in range(s):
                if W.coxetermat[s][t] == 3:
                    k = klstaroperation(W, s, t, [orb[o]])
                    if k is not False:
                        orb.append(k[0])
        o += 1
    return tuple([tuple(W.rightdescentsetperm(p)) for p in orb])


def checkgentau(W, maxd=10):
    for k in klcells(W, 1, v)[0]:
        t0 = generalisedtau(W, k[0])
        for i in k[1:]:
            if generalisedtau(W, i) != t0:
                print(k)
                return False
    return True

# gentauorbit2 (for use in gentaucells)


def gentauorbit2(W, l):
    orb = [l[:]]
    orb1 = set([x[:len(W.rank)] for x in orb[0]])
    for cell in orb:
        for s in W.rank:
            for t in range(s):
                if W.coxetermat[s][t] == 3:
                    nc = klstaroperation(W, s, t, cell)
                    if nc is not False:
                        rnd = [tuple(W.rightdescentsetperm(pw)) for pw in nc]
                        srnd = set(rnd)
                        if len(srnd) > 1:
                            return [[l[i] for i in range(len(l)) if rnd[i] == s]
                                    for s in srnd]
                        elif not nc[0][:len(W.rank)] in orb1:
                            orb.append(nc)
                            orb1.update([x[:len(W.rank)] for x in nc])
    return [l]

# Lusztig string operations (for use in gentaucells)
# product st has order 4


def klstringoperation4(W, s, t, pcell):
    pw1 = perminverse(pcell[0])
    if (pw1[s] >= W.N and pw1[t] >= W.N) or (pw1[s] < W.N and pw1[t] < W.N):
        return False
    nl = []
    H = reflectionsubgroup(W, [s, t])
    for pw in pcell:
        x = perminverse(redinrightcoset(W, H, perminverse(pw)))
        sx = tuple([W.permgens[s][r] for r in x])
        tsx = tuple([W.permgens[t][r] for r in sx])
        stsx = tuple([W.permgens[s][r] for r in tsx])
        if pw == sx:
            nl.append(stsx)
        elif pw == tsx:
            nl.append(tsx)
        elif pw == stsx:
            nl.append(sx)
        else:
            tx = tuple([W.permgens[t][r] for r in x])
            stx = tuple([W.permgens[s][r] for r in tx])
            tstx = tuple([W.permgens[t][r] for r in stx])
            if pw == tx:
                nl.append(tstx)
            elif pw == stx:
                nl.append(stx)
            elif pw == tstx:
                nl.append(tx)
            else:
                print('Mist')
    return nl

# product st has order 5


def klstringoperation5(W, s, t, pcell):
    pw1 = perminverse(pcell[0])
    if (pw1[s] >= W.N and pw1[t] >= W.N) or (pw1[s] < W.N and pw1[t] < W.N):
        return False
    nl = []
    H = reflectionsubgroup(W, [s, t])
    for pw in pcell:
        x = perminverse(redinrightcoset(W, H, perminverse(pw)))
        sx = tuple([W.permgens[s][r] for r in x])
        tsx = tuple([W.permgens[t][r] for r in sx])
        stsx = tuple([W.permgens[s][r] for r in tsx])
        tstsx = tuple([W.permgens[t][r] for r in stsx])
        if pw == sx:
            nl.append(tstsx)
        elif pw == tsx:
            nl.append(stsx)
        elif pw == stsx:
            nl.append(tsx)
        elif pw == tstsx:
            nl.append(sx)
        else:
            tx = tuple([W.permgens[t][r] for r in x])
            stx = tuple([W.permgens[s][r] for r in tx])
            tstx = tuple([W.permgens[t][r] for r in stx])
            ststx = tuple([W.permgens[s][r] for r in tstx])
            if pw == tx:
                nl.append(ststx)
            elif pw == stx:
                nl.append(tstx)
            elif pw == tstx:
                nl.append(stx)
            elif pw == ststx:
                nl.append(tx)
            else:
                print('Mist')
    return nl

# genstringorbit2 (Lusztig strings, strong star operations)


def genstringorbit2(W, l):
    orb = [l[:]]
    orb1 = set([x[:len(W.rank)] for x in orb[0]])
    for cell in orb:
        for s in W.rank:
            for t in range(s):
                nc = False
                if W.coxetermat[s][t] == 3:
                    nc = klstaroperation(W, s, t, cell)
                elif W.coxetermat[s][t] == 4:
                    nc = klstringoperation4(W, s, t, cell)
                elif W.coxetermat[s][t] == 5:
                    nc = klstringoperation5(W, s, t, cell)
                if nc is not False:
                    rnd = [tuple(W.rightdescentsetperm(pw)) for pw in nc]
                    srnd = set(rnd)
                    if len(srnd) > 1:
                        return [[l[i] for i in range(len(l)) if rnd[i] == s]
                                for s in srnd]
                    elif not nc[0][:len(W.rank)] in orb1:
                        orb.append(nc)
                        orb1.update([x[:len(W.rank)] for x in nc])
    return [l]

# kl liste der left cells, als perms


def checkh4(W, kl, verbose=False):
    ckl = [set(l) for l in kl]
    for cell in kl:
        for s in W.rank:
            for t in range(s):
                if W.coxetermat[s][t] == 5:
                    nc = klstringoperation5(W, s, t, cell)
                    if nc is not False and nc != cell:
                        if not set(nc) in ckl:
                            print('Mist')
                            return False
                        else:
                            if verbose:
                                lprint('.')
    return True

# gentaucells


def gentaucells(W, startset, verbose=False, lcells=False, string=False, tlen=False):
    """returns the partition  of a set of elements into equivalence
    classes  under  the  relation  given by Vogan's  generalised
    tau-invariant  (which amounts to repeated application of the
    star operations).  If the startset is known to be a union of
    left cells, the function performs faster when the additional
    argument 'lcells' is set to 'True'.

    >>> W = coxeter("E", 6)
    >>> g=gentaucells(W, allwords(W))  # not tested
    >>> len(g)                         # not tested
    652

    (In this case, the result is  precisely  the partition of  W
    into left cells; see the function  'klcells'.  The same also
    happens for W of type A, as shown in the original article of
    Kazhdan and Lusztig.)

    If the optional argument 'string' is set to 'True', then the
    function also uses Lustig's method of strings for generators
    s, t such that st has order bigger than 3  (see Section 10 in
    his article "Cells in affine Weyl groups I"). This is useful
    for dealing with groups of non simply-laced type:

    >>> W = coxeter("F", 4)
    >>> len(gentaucells(W, allwords(W), string=True))
    72

    (In this case again,  the result  is precisely the partition
    of W into left cells, for the equal parameter case.)

    See also 'klstarorbit' and 'gentaureps'.
    """
    if isinstance(startset[0], tuple):
        if len(startset[0]) == 2 * W.N:
            aset = startset
        else:
            aset = [W.coxelmtoperm(w) for w in startset]
    else:
        aset = [W.wordtoperm(w) for w in startset]
    if not lcells:
        pset = aset
    else:
        rset = leftklstarorbits(W, aset, lcells)
        pset = [l[0] for l in rset]
    if verbose:
        lprint('#I ' + str(len(pset)) + ' tau-cells: ')
    # new try: use additional function tlen which is constant on left cells
    # and returns a non-negative numerical value
    rd = []
    for pw in pset:
        pp = W.rightdescentsetperm(pw)
        if tlen is not False:
            pp.append(tlen(W, pw) + 10 * len(W.rank))
        rd.append(tuple(pp))
    # old version
    # rd = [tuple(W.rightdescentsetperm(pw)) for pw in pset]
    rest = [[pset[i] for i in range(len(pset)) if rd[i] == s] for s in set(rd)]
    res = []
    weiter = True
    while weiter:
        if verbose:
            lprint(str(len(res) + len(rest)) + ' ')
        if not string:
            cg = [gentauorbit2(W, r) for r in rest]
        else:
            cg = [genstringorbit2(W, r) for r in rest]
        weiter = False
        rest = []
        for i in range(len(cg)):
            if len(cg[i]) == 1:
                if not lcells:
                    res.append(cg[i][0])
                else:
                    neu = []
                    for x in cg[i][0]:
                        neu.extend(rset[pset.index(x)])
                    res.append(neu)
            else:
                rest.extend(cg[i])
                weiter = True
    if verbose:
        lprint('\n')
    return res

# F gentaureps


def gentaureps(W, verbose=False):
    """returns a set of the representatives of the generalised
    tau-cells under the star operations.

    >>> W = coxeter("E", 6)
    >>> g=gentaureps(W)
    >>> len(g)
    21
    >>> g1=[]
    >>> for x in g:
    ...     g1.extend(klstarorbit(W, x))
    >>> len(g1)
    652

    See also 'gentaucells' and 'klstarorbit'.
    """
    if W.order <= 2:
        nset = [[w] for w in allwords(W)]
    else:
        J = list(range(len(W.rank) - 1))
        W1 = reflectionsubgroup(W, J)
        dc = [W.coxelmtoperm(d) for d in redleftcosetreps(W, J)]
        nset = []
        cset = set()
        gt1 = gentaureps(W1)
        if verbose:
            lprint('#I ')
        for g in gt1:
            if verbose:
                lprint('+')
            l = []
            for x in g:
                wx = W.wordtoperm(x)
                for d in dc:
                    l.append(permmult(d, wx))
            if not all(permmult(p, p)[:len(W.rank)] != tuple(W.rank) or
                       p[:len(W.rank)] in cset for p in l):
                for gt in gentaucells(W, l, verbose=False, lcells=True):
                    if not any(x[:len(W.rank)] in cset for x in gt):
                        if verbose:
                            lprint('.')
                        nset.append([W.permtoword(p) for p in gt])
                        for o in klstarorbitperm(W, gt):
                            for e in o:
                                if permmult(e, e)[:len(W.rank)] == tuple(W.rank):
                                    cset.add(e[:len(W.rank)])
        if verbose:
            lprint(' ' + str(len(nset)) + ' reps\n')
    return nset

# klcellw0


def klcellw0(W, wgr):
    """returns the W-graph of a left cell multiplied by the longest
    element. (For the time being, only for equal parameters.)
    """
    w0 = longestperm(W)
    pc = [W.wordtoperm(w) for w in wgr.X]
    np = [permmult(p, w0) for p in pc]
    if np[0] in pc:
        return wgr
    else:
        ni = [W.leftdescentsetperm(p) for p in np]
        nmat = {}
        for k in wgr.mmat:
            nmat[(k[1], k[0])] = wgr.mmat[k]
        return wgraph(W, wgr.weights, [W.permtoword(p) for p in np], wgr.var,
                    ni, nmat, wgr.mpols, [p[:len(W.rank)] for p in np]).normalise()

# wgraphstarorbit


def wgraphstarorbit(W, wgr, gens='each'):
    """returns the orbit of a W-graph under the relation generated by the
    Kazhdan-Lusztig star operation.  (Only works  in the case of equal
    parameters.)

    >>> W = coxeter("A", 2); k=klcells(W, 1, v); k
    [[[[]], [[0, 1, 0]], [[1], [0, 1]], [[1, 0], [0]]],
     [wgraph(coxeter('A',2), [1, 1], [[]]),
      wgraph(coxeter('A',2), [1, 1], [[0, 1, 0]]),
      wgraph(coxeter('A',2), [1, 1], [[1], [0, 1]])]]
    >>> flatlist([wgraphstarorbit(W, g) for g in k[1]])
    [wgraph(coxeter('A',2), [1, 1], [[]]),
     wgraph(coxeter('A',2), [1, 1], [[0, 1, 0]]),
     wgraph(coxeter('A',2), [1, 1], [[1], [0, 1]]),
     wgraph(coxeter('A',2), [1, 1], [[0], [1, 0]])]

    See also 'klstaroperation', 'wgraph' and 'klcells'.
    """
    return [wgraph(W, wgr.weights, [W.permtoword(p) for p in l], wgr.var, wgr.Isets,
                   wgr.mmat, wgr.mpols, [p[:len(W.rank)] for p in l]).normalise()
            for l in klstarorbitperm(W, wgr.X, gens)]

# F klcellsun


def klcellsun(W, weightL, v, verbose=False):
    if isinstance(weightL, list):
        poids = weightL
    else:
        poids = len(W.rank) * [weightL]
    if len(W.rank) == 0:
        cr1 = [wgraph(W, poids, [[]], v, [[]], {}, [], [()])]
    else:
        J = list(W.rank)
        if W.cartantype[0][0] == 'E':
            J.remove(0)
        else:
            J.remove(len(W.rank) - 1)
        W1 = reflectionsubgroup(W, J)
        kk = klcellsun(W1, [poids[s] for s in J], v, verbose=False)
        if verbose and W.rank:
            lprint('#I ')
        if verbose:
            lprint('(' + str(len(kk)) + ') ')
        cr1 = []
        allmues = [[] for s in W.rank]
        for i in kk:
            if verbose:
                lprint('+')
            rk = relklpolsuneq(W, W1, i.wgraphtoklmat(), poids, v)
            for s in W.rank:
                for m in rk['mpols'][s]:
                    if m != 0 and m not in allmues[s]:
                        allmues[s].append(m)
            ind = wgraph(W, poids, rk, v).decompose()
            if verbose:
                lprint(str(len(ind)))
            for ii in ind:
                cr1.append(ii)
        if verbose:
            lprint('\n')
    if verbose and W.rank:
        lprint('#I ' + str(len(cr1)) + ' left cells, mues: ')
        for s in W.rank:
            lprint('[' + ', '.join(repr(i) for i in allmues[s]) + '] ')
        lprint('\n')
    cr1.sort(key=(lambda c: len(c.X)))
    return cr1


def klcells(W, weightL, v, allcells=True, verbose=False):
    """returns the partition of a finite Coxeter group into left cells
    together with the corresponding W-graphs.

    In the equal parameter case (where all weights are equal to 1),
    the function returns a pair [l, l1] where l is a list describing
    the partition of W into left cells and  l1 is a list containing
    the  W-graphs for a set of a representatives  of the left cells
    under the equivalence relation given by the star operation. (It
    is known that  star equivalent left cells give rise to the same
    W-graphs.) The computation is done recursively, using induction
    of left cells from proper parabolic subgroups (see the function
    'relklpols'). This works very efficiently for groups of rank up
    to 6, including types H4 and E6. If one is  willing to wait for
    a few hours,  then type E7  is  also possible.  If the optional
    argument 'allcells' is set to 'False',  then for each left cell
    the function  only returns  those elements whose inverses  also
    lie in that left cell.

    In the case of unequal parameters,  we just return the W-graphs
    corresponding to all the left cells of W.

    See   also   'klpolynomials',   'wgraphstarorbit',  'reklpols',
    'wgraph', 'gentaucells' and 'twosidedcells'.

    >>> klcells(coxeter("B", 3), [2, 1, 1], v)  # unequal parameters
    [wgraph(coxeter('B',3), [2, 1, 1], [[]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0], [1, 0], [2, 1, 0]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[1], [2, 1]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[2], [1, 2]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 1], [1, 0, 1], [2, 1, 0, 1]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 2], [1, 0, 2], [0, 1, 0, 2],
                              [1, 2, 1, 0], [0, 1, 2, 1, 0], [1, 0, 1, 2, 1, 0]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 1, 0], [0, 2, 1, 0], [1, 0, 2, 1, 0],
                                                    [0, 1, 0, 2, 1, 0]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 1, 2], [1, 0, 1, 2], [2, 1, 0, 1, 2]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 2, 1], [1, 0, 2, 1], [0, 1, 0, 2, 1],
                        [1, 2, 1, 0, 1], [0, 1, 2, 1, 0, 1], [1, 0, 1, 2, 1, 0, 1]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[1, 2, 1], [0, 1, 2, 1], [1, 0, 1, 2, 1],
                                                    [1, 2, 1, 0, 1, 2]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 1, 0, 1], [0, 2, 1, 0, 1],
                                                    [1, 0, 2, 1, 0, 1]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 1, 0, 1, 2], [0, 2, 1, 0, 1, 2],
                                                  [1, 0, 2, 1, 0, 1, 2]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 1, 0, 1, 2, 1], [0, 1, 2, 1, 0, 1, 2],
                                                [1, 0, 1, 2, 1, 0, 1, 2]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 1, 0, 1, 2, 1, 0], [0, 1, 0, 2, 1, 0, 1, 2]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 1, 0, 2, 1, 0, 1], [0, 1, 0, 1, 2, 1, 0, 1]]),
     wgraph(coxeter('B',3), [2, 1, 1], [[0, 1, 0, 1, 2, 1, 0, 1, 2]])]

    Here  are some examples for equal parameters,  where the more
    efficient algorithm based on 'relklpols' is used.

    >>> klcells(coxeter("I5", 2), 1, v)
    [[[[]],
     [[0, 1, 0, 1, 0]],
     [[1], [0, 1], [1, 0, 1], [0, 1, 0, 1]],
     [[0], [1, 0], [0, 1, 0], [1, 0, 1, 0]]],
    [wgraph(coxeter('I5',2), [1, 1], [[]]),
     wgraph(coxeter('I5',2), [1, 1], [[0, 1, 0, 1, 0]]),
     wgraph(coxeter('I5',2), [1, 1], [[1], [0, 1], [1, 0, 1], [0, 1, 0, 1]]),
     wgraph(coxeter('I5',2), [1, 1], [[0], [1, 0], [0, 1, 0], [1, 0, 1, 0]])]]

    >>> k=klcells(coxeter("H", 4), 1, v)     # long time    # takes < 7 minutes
    #I 206 left cells (90 non-equivalent), mues: 1, 2, 3
    >>> set([len(c) for c in k[0]])       # long time
    set([32, 1, 36, 326, 8, 392, 18, 436, 25])

    (Thus, W has left cells of size 1, 8, 18, 25, 33, 36, 326, 392, 436.)

    The left cells in  type  H4 were first determined by

       D. Alvis: The left cells of the Coxeter group of type H_4,
                 J. Algebra 107 (1987), 160-168; see also
                 http://mypage.iusb.edu/~alvis/h4data

    (I have checked that the result of 'klcells' indeed coincides
    with Alvis' tables. Note that Alvis can actually compute  all
    the Kazhdan-Lusztig polynomials in type H4,  which would take
    a very long time with  'klpolynomials'.  If one is interested
    in  reproducing  this information,  then it is better to  use
    DuCloux's Coxeter programme. Alternatively, one can also build
    all Kazhdan-Lusztig polynomials from the relative polynomials
    returned by 'allrelklpols'; this takes about 1 day cpu time.)

    >>> k=klcells(coxeter("E", 6), 1, v)    # takes about 45 seconds
    >>> set([len(c) for c in k[0]])
    {1, 6, 20, 24, 45, 60, 64, 81, 150, 230, 280}

    (I have checked that the result of  'klcells'  coincides with
    the result for E6 produced by DuCloux's Coxeter programme.)

    >>> k=klcells(coxeter("D", 7), 1, v)    # not tested # takes < 4 minutes
    >>> set([len(c) for c in k[0]])      # not tested
    set([1, 98, 35, 6, 7, 105, 231, 140, 15, 112, 49, 210, 147, 20, 21, 56, 84,
         154, 175, 63])

    >>> k=klcells(coxeter("E", 7), 1, v)    # not tested # takes about 4 hours
    >>> set([len(c) for c in k[0]])      # not tested
    set([1024, 1, 27, 7, 168, 105, 756, 135, 77, 910, 621, 504, 210, 594, 21,
         225, 665, 378, 91, 189, 875])

    >>> k=klcells(coxeter("D", 8), 1, v)    # not tested # takes about 4 hours
    >>> set([len(c) for c in k[0]])      # not tested
    set([1, 7, 8, 140, 21, 1302, 280, 28, 35, 168, 176, 392, 434, 56, 315, 700,
         448, 68, 714, 76, 336, 184, 980, 728, 350, 230, 616, 490, 364, 238,
         112, 504, 250, 252])

    >>> k=klcells(coxeter("A", 9), 1, v)    # not tested # takes about 50 minutes
    >>> set([len(c) for c in k[0]])      # not tested
    set([768, 1, 9, 525, 160, 35, 36, 42, 300, 567, 315, 448, 288, 450, 75, 210,
         84, 90, 350, 225, 252, 126])

    The  program  essentially  works  in all cases  where one can
    afford  to keep a  complete list  of all elements of W in the
    main memory.  Thus, type  B8 with its  10, 321, 920 elements is
    about the limit:  it takes some  58 hours and  9GB  memory to
    compute the 15304 left cells and the corresponding W-graphs.
    """
    if isinstance(weightL, list):
        poids = weightL
    else:
        poids = len(W.rank) * [weightL]
    if any(i < 0 for i in poids):
        raise ValueError('all parameters must be non-negative')
    if all(i == 1 for i in poids):
        if len(W.rank) == 0:
            nc = [[[]]]
            cr1 = [wgraph(W, poids, [[]], v, [[]], {}, [], [()])]
            creps = [()]
        else:
            allmues = []
            J = list(W.rank)
            if W.cartantype[0][0] == 'E' and len(W.cartantype[0][1]) == 7:
                J.remove(0)
            else:
                J.remove(len(W.rank) - 1)
            W1 = reflectionsubgroup(W, J)
            X1p = [W.coxelmtoword(x1) for x1 in redleftcosetreps(W, J)]
            kk = klcells(W1, [poids[s] for s in J], v, verbose=False, allcells=False)
            if verbose and W.rank:
                lprint('#I ')
            if verbose:
                lprint('(' + str(len(kk[0])) + ':' + str(len(kk[1])) + ') ')
            nc, cr1, creps = [], [], []
            celms = set()
            i, tot = 0, 0
            while tot < W.order:
                if verbose:
                    lprint('+')
                pairs = [W.wordtoperm(ci[0] + ci[1]) for ci in cartesian(X1p,
                                      [[J[s] for s in w] for w in kk[1][i].X])]
                if verbose and all(permmult(pa, pa)[:len(W.rank)] != tuple(W.rank) or
                                   pa[:len(W.rank)] in celms for pa in pairs):
                    lprint(str(0))
                else:
                    rk = relklpols(W, W1, kk[1][i].wgraphtoklmat(), 1, v)
                    for m in rk['mpols']:
                        if m != 0 and m not in allmues:
                            allmues.append(m)
                    if len(rk['perm']) > 300:
                        if len(rk['perm']) > 1500:
                            rht = [generalisedtau(W, p, maxd=3 * len(W.rank))
                                   for p in rk['perm']]
                        else:
                            rht = [tuple(W.rightdescentsetperm(p))
                                   for p in rk['perm']]
                        srht = list(set(rht))
                        ind1 = wgraph(W, poids, rk, v)
                        if verbose:
                            lprint(str(len(srht)) + '!')
                        ind = []
                        for rh in srht:
                            l = [x for x in range(len(rht)) if rht[x] == rh]
                            x1 = [ind1.X[ih] for ih in l]
                            x1r = [ind1.Xrep[ih] for ih in l]
                            i1 = [ind1.Isets[ih] for ih in l]
                            m1 = {}
                            for kh in ind1.mmat:
                                if kh[0] in l and kh[1] in l:
                                    m1[(l.index(kh[0]), l.index(kh[1]))
                                       ] = ind1.mmat[kh]
                            ind.extend(wgraph(ind1.W, ind1.weights, x1, ind1.var, i1,
                                              m1, ind1.mpols, x1r).decompose())
                    else:
                        ind = wgraph(W, poids, rk, v).decompose()
                    if verbose:
                        lprint(str(len(ind)))
                    for ii in ind:
                        if tot < W.order and not any(xii in celms for xii in ii.Xrep):
                            creps.append(ii.Xrep[0])
                            cr1.append(ii)
                            for o in klstarorbitperm(W, ii.X):
                                # g=wgraph(W, ii.weights, [W.permtoword(x) for x in o], ii.var,
                                #                  ii.Isets, ii.mmat, ii.mpols, [x[:len(W.rank)]
                                #                                     for x in o]).normalise()
                                # nc.append(g)
                                # for e in g.Xrep:  celms.add(e)
                                if allcells:
                                    nc.append([W.permtoword(x) for x in o])
                                else:
                                    nc.append([W.permtoword(x) for x in o
                                               if perminverse(x) in o])
                                for e in o:
                                    if permmult(e, e)[:len(W.rank)] == tuple(W.rank):
                                        celms.add(e[:len(W.rank)])
                                tot += len(o)
                        if verbose:
                            lprint('.')
                        if tot < W.order:
                            ii0 = klcellw0(W, ii)
                            if not any(xii0 in celms for xii0 in ii0.Xrep):
                                creps.append(ii0.Xrep[0])
                                cr1.append(ii0)
                                for o in klstarorbitperm(W, ii0.X):
                                    # g=wgraph(W, ii0.weights, [W.permtoword(x) for x in o],
                                    #                 ii0.var, ii0.Isets, ii0.mmat, ii0.mpols,
                                    #                  [x[:len(W.rank)] for x in o]).normalise()
                                    # nc.append(g)
                                    # for e in g.Xrep:  celms.add(e)
                                    if allcells:
                                        nc.append([W.permtoword(x) for x in o])
                                    else:
                                        nc.append([W.permtoword(x) for x in o
                                                   if perminverse(x) in o])
                                    for e in o:
                                        if permmult(e, e)[:len(W.rank)] == tuple(W.rank):
                                            celms.add(e[:len(W.rank)])
                                    tot += len(o)
                i += 1
        if verbose:
            lprint('\n')
        if verbose and W.rank:
            lprint('#I ' + str(len(nc)) + ' left cells (')
            lprint(str(len(creps)) + ' non-equivalent), ')
            lprint('mues: ' + ', '.join(str(i) for i in allmues) + '\n')
        # nc.sort(key=(lambda c:len(c)))
        ct = chartable(W)
        if allcells and len(nc) != sum([ct['irreducibles'][i][0]
                     for i in range(len(ct['a'])) if ct['a'][i] == ct['b'][i]]):
            print("Mist!")
            return False
        cr1.sort(key=(lambda c: len(c.X)))
        return [nc, cr1]
    else:
        return klcellsun(W, weightL, v, verbose=False)
        # k=klpolynomials(W, weightL, v)
        # return [wgraph(W, poids, {'elms':[k['elms'][x] for x in c],
        #          'mpols':k['mpols'], 'klpols':k['klpols'],
        #           'klmat':[[k['klmat'][c[w]][c[y]] for y in range(w+1)]
        #             for w in range(len(c))]}, v) for c in k['lcells']]


def zeroterm(p):
    if isinstance(p, int):
        return p
    if p.val > 0 or not p.coeffs:
        return 0
    return p.coeffs[0]


# F leadingcoefficients
def leadingcoefficients(W, weightL, lw, clpols=None):
    """returns  the  leading coefficients  (as  defined by  Lusztig)  of the
    character values of the generic Iwahori-Hecke algebra associated with
    W and given list of weights. For an irreducible representation E  and
    w in W, the coefficient c_{w, E} is defined by

       Tr(T_w, E) = c_{w, E} v^(-a_E) + higher powers of v,

    where  a_E is the a-invariant of E (see 'ainvariants').  The argument
    lw  contains  the  list  of  elements,  given as reduced expressions,
    for  which the  leading values  are to be  computed.  The weights are
    specified as described in  'ainvariants'.  The  computations  use the
    character table of  the Iwahori--Hecke algebra (see 'heckechartable')
    and the class polynomials (see 'heckecharvalues').

    (Note that Lusztig actually further multiplies c_{w, E}  by (-1)^l(w),
    but we omit this sign here.)

    The  argument weightL specifies a weight function  as explained
    in 'ainvariants';  in particular,  the programme also works for
    unequal parameters.

    >>> W = coxeter("B", 2)
    >>> a=allwords(W); a;
    [[], [0], [1], [0, 1], [1, 0], [0, 1, 0], [1, 0, 1], [0, 1, 0, 1]]

    >>> leadingcoefficients(W, [1, 1], a)
    [[0, 0, 0, 1, 0],
     [-1, -1, 0, 0, 0],
     [0, -1, 0, 0, -1],
     [0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0],
     [1, -1, 0, 0, 0],
     [0, -1, 0, 0, 1],
     [0, 0, 1, 0, 0]]

    See also 'leftcellleadingcoeffs'.
    """
    v = lpol([1], 1, 'v')
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL[:]
    ti = heckechartable(W, [v**i for i in poids])['irreducibles']
    ainv = ainvariants(W, poids)
    maxl = max(len(w) for w in lw)
    if clpols is None:
        cpmat = allclasspolynomials(W, [v**(2 * p) for p in poids], maxl)
    else:
        cpmat = clpols
    lc = []
    for w in lw:
        cind = 0
        for i in w:
            cind += poids[i]
        cp = cpmat[W.wordtocoxelm(w)]
        # lc.append([zeroterm((-1)**len(w)*v**(ainv[i]-cind)*sum(cp[j]*ti[i][j]
        #        for j in range(len(ainv)))) for i in range(len(ainv))])
        lc.append([zeroterm(v**(ainv[i] - cind) * sum(cp[j] * ti[i][j]
                for j in range(len(ainv)))) for i in range(len(ainv))])
    return lc

# F leftcellleadingcoeffs


def leftcellleadingcoeffs(W, weightL, v, cell, clpols=[], newnorm=False):
    """returns  a dictionary with information  concerning  the leading
    coefficients in a given left cell. The components are:

    - elms    : the list of all w in the cell such that w^(-1) also
      lies in the cell;
    - ti      : the associated character table;
    - distinv : the distinguished involution in the cell;
    - nd      : the corresponding sign;
    - special : the character for which all values are positive;
    - char    : decomposition into irreducible characters of W.

    More precisely,  let  C  be a left cell.  Then  we consider the
    subalgebra of the asymptotic algebra J which is spanned  by all
    basis elements  t_w where both  w and its inverse lie in C. The
    associated character table is the table of values

                ((-1)^l(d) n_d c_{w, E})_{E, w}

    where  w runs over all w in C such that w^{-1} in C, and E runs
    over all E in Irr(W) such that E occurs in the left cell module
    given by C.  Here,  c_{w, E} are the leading coefficients of the
    character  values  of  the corresponding  generic Iwahori-Hecke
    algebra as defined by::

        G. Lusztig, Leading coefficients of character values of Hecke
        algebras, Proc. Symp. Pure Math. 47, AMS, 1987, pp. 235-262.

    (This  article  also contains a detailed study of the character
    tables (c_{w, E}) in the equal parameter case.)

    The distinguished involution d and the corresponding  sign 'nd'
    are uniquely  determined by the  condition  that  nd*t_d is the
    identity element of the above subalgebra. It is known that nd=1
    in the equal parameter case;  in  the general unequal parameter
    case, these properties are conjectural.  (In fact, the function
    checks if such a distinguished involution exists.)

    The  argument weightL specifies a weight function  as explained
    in 'ainvariants';  in particular,  the programme also works for
    unequal parameters.

    >>> v = lpol([1], 1, 'v')
    >>> W = coxeter("B", 2)
    >>> [leftcellleadingcoeffs(W, 1, v, l)
    ...          for l in klcells(W, 1, v)[0]] # equal parameters
    [{'elms': [[]], 'nd': 1, 'special': ('[[2], []]',),
      'distinv': [], 'ti': [[('[[2], []]',), [1]]]},
     {'elms': [[0, 1, 0, 1]], 'nd': 1, 'special': ('[[], [1, 1]]',),
      'distinv': [0, 1, 0, 1], 'ti': [[('[[], [1, 1]]',), [1]]]},
     {'elms': [[1], [1, 0, 1]], 'nd': 1, 'special': ('[[1], [1]]',),
      'distinv': [1], 'ti': [[('[[1], [1]]',), [1, 1]],
      [('[[], [2]]',), [1, -1]]]},
     {'elms': [[0], [0, 1, 0]], 'nd': 1, 'special': ('[[1], [1]]',),
      'distinv': [0], 'ti': [[('[[1, 1], []]',), [1, -1]],
      [('[[1], [1]]',), [1, 1]]]}]

    >>> [leftcellleadingcoeffs(W, [2, 1], v, l.X)
    ...            for l in klcells(W, [2, 1], v)]  # unequal parameters
    [{'elms': [[]], 'nd': 1, 'special': ('[[2], []]',),
      'distinv': [], 'ti': [[('[[2], []]',), [1]]]},
     {'elms': [[0]], 'nd': 1, 'special': ('[[1], [1]]',),
      'distinv': [0], 'ti': [[('[[1], [1]]',), [1]]]},
      {'elms': [[1]], 'nd': 1, 'special': ('[[], [2]]',),
       'distinv': [1], 'ti': [[('[[], [2]]',), [1]]]},
      {'elms': [[1, 0, 1]], 'nd': 1, 'special': ('[[1], [1]]',),
       'distinv': [1, 0, 1], 'ti': [[('[[1], [1]]',), [1]]]},
      {'elms': [[0, 1, 0]], 'nd': -1, 'special': ('[[1, 1], []]',),
       'distinv': [0, 1, 0], 'ti': [[('[[1, 1], []]',), [1]]]},
      {'elms': [[0, 1, 0, 1]], 'nd': 1, 'special': ('[[], [1, 1]]',),
       'distinv': [0, 1, 0, 1], 'ti': [[('[[], [1, 1]]',), [1]]]}]

    (Note the negative value for nd.)

    Remark:  The normalisation by the sign  (-1)^l(d)*n_d  has the
    effect that the above table  has a row in which all entries are
    strictly positive numbers.  (There can be at  most one row with
    this property.)  It is known that, in the equal parameter case,
    this row  is labelled by  the unique special character  (in the
    sense of Lusztig) which appears in the left cell representation
    carried by C.

    >>> W = coxeter("F", 4); k=klcells(W, 1, v)
    >>> l = leftcellleadingcoeffs(W, 1, v, k[0][64]); l['ti']
    [[('4_1',), [1, -1, -1, 1, 1, 0, -1, -1, 1]],
     [('9_2',), [1, 1, -1, -1, -1, 0, -1, 1, 1]],
     [('9_3',), [1, -1, 1, -1, -1, 0, 1, -1, 1]],
     [('6_2',), [1, 1, 1, 1, 1, -2, 1, 1, 1]],
     [('12',), [1, 1, 1, 1, 1, 4, 1, 1, 1]],
     [('16',), [2, 0, 0, 0, 0, 0, 0, 0, -2]]]
    >>> l['special']
    ('12',)
    >>> t = chartable(W); t['charnames'].index('12')
    15
    >>> t['a'][15]; t['b'][15]
    4
    4

    (Thus, indeed, the character labelled by '12' is special in the
    sense originally defined by Lusztig.)

    See  also 'chartable', 'leadingcoeffients', 'klcells',
    'allcellsleadingcoeffs' and 'distinguishedinvolutions'.
    """
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL[:]
    ch = chartable(W, chars=False)['charnames']
    fshi = [s.coeffs[0] for s in schurelms(W, [v**p for p in poids])]
    pcell = [W.wordtoperm(w) for w in cell]
    lw = [cell[i] for i in range(len(cell)) if perminverse(pcell[i]) in pcell]
    if clpols == []:
        cpmat = allclasspolynomials(W, [v**(2 * p) for p in poids],
                                    max(len(w) for w in lw))
    else:
        cpmat = clpols
    lc = transposemat(leadingcoefficients(W, weightL, lw, cpmat))
    ii = list(filter(lambda i: any(x != 0 for x in lc[i]), range(len(fshi))))
    ftot = 1
    for i in ii:
        ftot *= fshi[i]
    cof = []
    for i in ii:
        cf = 1
        for j in ii:
            if i != j:
                cf *= fshi[j]
        cof.append(cf)
    nd = [(-1)**len(lw[w]) * sum(cof[i] * lc[ii[i]][w]
               for i in range(len(ii))) // ftot for w in range(len(lw))]
    # nd1=[(-1)**len(lw[w])*sum((W.order*lc[i][w])//fshi[i]
    #       for i in range(len(fshi)))//W.order for w in range(len(lw))]
    # if nd1!=nd:
    #  print('mist!')
    #  return False
    if nd.count(0) != len(nd) - 1:
        print("no distinguished involution!")
        return nd
    i = 0
    while nd[i] == 0:
        i += 1
    di = i
    if nd[di]**2 != 1:
        print("no distinguished involution!!")
        return [di, nd, nd[di]**2]
    if nd[di] == -1:
        lc = [[-i for i in l] for l in lc]
    if len(lw[di]) % 2 == 1:
        lc1 = [[-i for i in l] for l in lc]
    else:
        lc1 = lc
    lc = [[(-1)**len(lw[i]) * l[i] for i in range(len(lw))] for l in lc]
    if not all(l[di] >= 0 for l in lc):
        print('identity not OK for NEW normalisation')
    if not all(l[di] >= 0 for l in lc1):
        print('identity not OK for OLD normalisation')
    # if set([(len(x)-len(lw[di]))%2 for x in lw])!=set([0]):
    #  lprint('#W odd lengths ')
    sp = 0
    while sp < len(ii) and not all(x > 0 for x in lc[ii[sp]]):
        sp += 1
    if sp == len(ii):
        print('no special character!')
    chi = []
    for i in range(len(fshi)):
        if i in ii:
            chi.append(lc[i][di])
        else:
            chi.append(0)
    if newnorm:
        return {'ti': [[ch[i], lc[i]] for i in ii], 'distinv': lw[di],
                'nd': nd[di], 'elms': lw, 'special': ch[ii[sp]], 'char': chi}
    else:
        return {'ti': [[ch[i], lc1[i]] for i in ii], 'distinv': lw[di],
                'nd': nd[di], 'elms': lw, 'special': ch[ii[sp]], 'char': chi}


# F poltostr
def poltostr(f):
    if isinstance(f, int):
        return '0.' + str(f)
    if not f.coeffs:
        return '0.0'
    return str(f.val) + '.' + '.'.join(str(i) for i in f.coeffs)


# F strtopol
def strtopol(sp, vnam):
    spl = sp.split('.')
    return lpol([int(i) for i in spl[1:]], val=int(spl[0]), vname=vnam)


# F distinguishedinvolutions
def distinguishedinvolutions(W, weightL, distonly=True, verbose=False):
    """returns the list of distinguished involutions with respect to a
    weight function, plus some additional information (as explained
    below). Here, we use the following  definition:

    An element w in W is called distinguished if

       n_w := (-1)^l(w) * sum_{E in Irr(W)} f_E^(-1) c_{w, E}

    is non-zero, where  c_{w, E} are the leading coefficients of the
    character values of the generic  Iwahori-Hecke algebra  and f_E
    are defined in terms of the corresponding Schur elements.  This
    definition appeared in

      M. Geck, Leading coefficients and cellular bases of Hecke
      algebras, Proc. Edinburgh Math. Soc. 52 (2009), 653--677.

    (This  is equivalent  to  Lusztig's  original definition in the
    case of equal parameters and also in  types I_2(m), F_4 for any
    choice of parameters;  it is conjectured  that this equivalence
    holds in general.)

    One expects that all distinguished elements are involutions and
    that every left cell with respect to the given weight  function
    contains exactly one distinguished element.  (This  is known to
    be true in the equal parameter case where it is also known that
    n_d=1 for all distinguished d in W.)

    The function  returns  a list whose first component is the list
    of distinguished involutions and the second component is a list
    of pairs

        (E_i, c_{d, E_i})   where E_i in Irr(W) and c_{d, E_i}<>0.

    If not all n_d are equal to 1,  then there is a third component
    containing the values n_d.

    >>> W = coxeter("I8", 2)
    >>> distinguishedinvolutions(W, [1, 2])   # unequal parameters
    [[[], [1], [0], [0, 1, 0], [1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1]],
     [[[('phi_{1, 0}',), 1]],
      [[('phi_{2, 3}',), -1], [('phi_{2, 2}',), -1], [('phi_{2, 1}',), -1]],
      [[("phi_{1, 4}''",), -1]],
      [[('phi_{2, 3}',), -1], [('phi_{2, 2}',), -1], [('phi_{2, 1}',), -1]],
      [[("phi_{1, 4}'",), 1]],
      [[('phi_{1, 8}',), 1]]],
     [1, 1, 1, 1, -1, 1]]

    >>> W = coxeter("G", 2)
    >>> distinguishedinvolutions(W, 1)       # equal parameters
    [[[], [1], [0], [0, 1, 0, 1, 0, 1]],
     [[[('phi_{1, 0}',), 1]],
      [[('phi_{2, 2}',), -1], [('phi_{2, 1}',), -1], [("phi_{1, 3}''",), -1]],
      [[('phi_{2, 2}',), -1], [('phi_{2, 1}',), -1], [("phi_{1, 3}'",), -1]],
      [[('phi_{1, 6}',), 1]]]]

    (Here, all signs n_d are known to be equal to 1.)

    This function even works for  W of large rank:  For type H4, it
    takes about  25s;  for type E6, about  45s;  for type E7, about
    40min; for type E8, about  18 days (and 22GB main memory).

    See  also  'distinguishedinvolutions_eq'  (optimised  for equal
    parameters),  'libdistinv', 'distinva',  'leadingcoefficients',
    'schurelms' and 'leftcellleadingcoeffs'.

    Final remark: There is an optional argument 'distonly'. If this
    is set to 'False',  then  the function returns similar lists as
    described above, but now the first list contains all elements w
    such that c_{w, E} is non-zero for some E in Irr(W). Hence, this
    yields the complete table of all leading coefficients c_{w, E}.
    """
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL[:]
    v = lpol([1], 1, 'v')
    poin = poincarepol(W, v).coeffs
    w0 = longestperm(W)
    ct = chartable(W)
    lcl = [len(w) for w in conjugacyclasses(W)['reps']]
    vs = [v**p for p in poids]
    ti = heckechartable(W, vs)['irreducibles']
    schur = schurelms(W, vs)
    fshi = [s.coeffs[0] for s in schur]
    ainv = [-s.val // 2 for s in schur]
    tup = [[i, ainv[i]] for i in range(len(ainv))]
    tup.sort(key=(lambda i: i[1]), reverse=True)
    ti = [ti[tup[i][0]] for i in range(len(ainv))]
    fshi = [fshi[tup[i][0]] for i in range(len(ainv))]
    ainv = [ainv[tup[i][0]] for i in range(len(ainv))]
    chn = [ct['charnames'][tup[i][0]] for i in range(len(ainv))]
    ti1 = [ct['irreducibles'][tup[i][0]] for i in range(len(ainv))]
    signchar = [(-1)**lw for lw in lcl]
    signp = [ti1.index([l[j] * signchar[j] for j in range(len(lcl))]) for l in ti1]
    maxl = W.N
    if W.N in lcl:
        iw0 = lcl.index(W.N)
        eps = [x[iw0] // x[0] for x in ct['irreducibles']]
        eps = [eps[tup[i][0]] for i in range(len(ainv))]
        maxl = W.N // 2
    distinv, nvec = [[]], [1]
    lc = [zeroterm(v**(ainv[i]) * ti[i][0]) for i in range(len(ainv))]
    char = []
    for i in range(len(ainv)):
        if lc[i] != 0:
            char.append([chn[i], lc[i]])
        # if lc[i]>0:
        #  char.append([chn[i], lc[i]])
        # elif lc[i]<0:
        #  char.append([chn[i], -lc[i]])
    charvec = [char[::-1]]
    if maxl == W.N or all(p == 0 for p in poids):
        distinv0, nvec0, charvec0 = [], [], []
    else:
        distinv0, nvec0 = [W.permtoword(w0)], [1]
        Lw0 = ainv[ti1.index(signchar)]
        lc0 = [zeroterm(v**(ainv[i] - Lw0) * ti[i][iw0]) for i in range(len(ainv))]
        char0 = []
        for i in range(len(ainv)):
            if lc0[i] != 0:
                char0.append([chn[i], lc0[i]])
            # if lc0[i]>0:
            #  char0.append([chn[i], lc0[i]])
            # elif lc0[i]<0:
            #  char0.append([chn[i], -lc0[i]])
        charvec0 = [char0[::-1]]
    cpmat = []
    cp = len(ainv) * [0]
    cp[0] = 1
    cpmat.append({bytes(W.rank): ';'.join(poltostr(f) for f in cp)})
    cps = {}
    nega = False
    zael = 0
    if verbose:
        lprint('#I length  0 - 1 element, 1 class polynomial; 1 distinv\n')
    for l in range(maxl):
        if verbose:
            if l < 9:
                lprint('#I length  ' + str(l + 1))
            else:
                lprint('#I length ' + str(l + 1))
        nl = set()
        if l == 0:
            ol = []
        else:
            ol = set(cpmat[l - 1])
        for w in cpmat[l]:
            for s in W.permgens:
                nw = bytes([s[i] for i in w])
                if nw not in ol:
                    nl.add(nw)
            if len(nl) == poin[l + 1]:
                break
        cps = {}
        if verbose:
            lprint(' - ')
        ll = len(nl)
        spols = []
        while nl:
            w = W.coxelmtoword(next(iter(nl)))
            pw = W.wordtoperm(w)
            pw1 = perminverse(pw)
            t = testcyclicshift1(W, w, pw)
            if t[0] == 1:
                cp = len(ainv) * [0]
                cp[t[2]] = 1
            else:
                cp1 = [strtopol(f, 'v')
                       for f in cpmat[l - 1][bytes(t[2])].split(';')]
                cp2 = [strtopol(f, 'v') for f in cpmat[l][bytes([W.permgens[t[3]][i]
                                                        for i in t[2]])].split(';')]
                if poids[t[3]] == 1:
                    cp = [v * cp1[i] + (v - 1) * cp2[i] for i in range(len(ainv))]
                else:
                    cp = [v**(poids[t[3]]) * cp1[i] + (v**(poids[t[3]]) - 1) * cp2[i]
                          for i in range(len(ainv))]
            strcp = ';'.join(poltostr(f) for f in cp)
            ic = len(spols) - 1
            while ic >= 0:
                if strcp == spols[ic]:
                    break
                ic -= 1
            if ic == -1:
                spols.append(strcp)
            for x in t[1]:
                cx = x[:len(W.rank)]
                cps[bytes(cx)] = spols[ic]
                nl.remove(bytes(cx))
            if pw1 not in t[1]:
                for x in t[1]:
                    cx = perminverse(x)[:len(W.rank)]
                    cps[bytes(cx)] = spols[ic]
                    nl.remove(bytes(cx))
            if len(t[1]) == 1 and (any(p != 1 for p in poids) or W.permorder(pw) == 2
                                or generalisedtau(W, pw, maxd=len(W.rank)**2) ==
                                   generalisedtau(W, pw1, maxd=len(W.rank)**2)):
                zael += 1
                cpv = []
                for j in range(len(ainv)):
                    if isinstance(cp[j], int):
                        cpv.append(cp[j])
                    elif cp[j].coeffs == []:
                        cpv.append(0)
                    else:
                        cpv.append(cp[j].value(v**2))
                cind = 0
                for i in w:
                    cind += poids[i]
                lc = []
                nonz = -1
                for i in range(len(ainv)):
                    if ainv[i] > cind or (nonz != -1 and nonz != ainv[i]):
                        lcc = 0
                    else:
                        lcc = zeroterm(v**(ainv[i] - cind) * sum(cpv[j] * ti[i][j]
                                          for j in range(len(ainv)) if cpv[j] != 0))
                        if nonz == -1 and lcc != 0:
                            nonz = ainv[i]
                    lc.append(lcc)
                ii = [i for i in range(len(ainv)) if lc[i] != 0]
                if ii != []:
                    ftot = 1
                    for i in ii:
                        ftot *= fshi[i]
                    cof = []
                    for i in ii:
                        cf = 1
                        for j in ii:
                            if i != j:
                                cf *= fshi[j]
                        cof.append(cf)
                    nd = (-1)**len(w) * sum(cof[i] * lc[ii[i]]
                        for i in range(len(ii)))
                    if nd % ftot == 0:
                        nd = nd // ftot
                    else:
                        print("Mist!")
                        return False
                    if nd != 0 or distonly is not True:
                        distinv.append(w)
                        nvec.append(nd)
                        char = []
                        for i in range(len(ainv)):
                            if lc[i] != 0:
                                char.append([chn[i], lc[i]])
                            # if lc[i]>0:
                            #  char.append([chn[i], lc[i]])
                            # elif lc[i]<0:
                            #  char.append([chn[i], -lc[i]])
                        charvec.append(char[::-1])
                        if nega is False and nd != 1:
                            nega = True
                    if maxl == W.N // 2 and (W.N % 2 == 1 or l < maxl - 1):
                        nd = sum(eps[ii[i]] * cof[i] * lc[ii[i]]
                               for i in range(len(ii)))
                        if nd % ftot == 0:
                            nd = nd // ftot
                        else:
                            print("Mist!")
                            return False
                        if nd != 0 or distonly is not True:
                            distinv0.append(W.permtoword([w0[i] for i in pw]))
                            nvec0.append(nd)
                            char0 = []
                            for i in range(len(ainv)):
                                if lc[i] != 0:
                                    char0.append(
                                        [signp[i], (-1)**(W.N + len(w)) * eps[i] * lc[i]])
                                # if lc[i]>0:
                                #  char0.append([signp[i], lc[i]])
                                # elif lc[i]<0:
                                #  char0.append([signp[i], -lc[i]])
                            char0.sort(key=(lambda i: i[0]), reverse=True)
                            charvec0.append([[chn[i[0]], i[1]] for i in char0])
                            if nega is False and nd != 1:
                                nega = True
        if verbose:
            lprint(str(ll) + ' elements, ' + str(len(spols)) + ' class polynomials; ')
            lprint(str(len(distinv) + len(distinv0)) + ' distinvs\n')
        if l > 0:
            cpmat[l - 1] = 0
        cpmat.append(cps)
    distinv = distinv + distinv0[::-1]
    nvec = nvec + nvec0[::-1]
    charvec = charvec + charvec0[::-1]
    # d1=distinguishedinvolutions(W, poids)
    # d1=libdistinv(W, poids)
    # if not (len(distinv)==len(d1) and all(i in d1 for i in distinv)):
    #  print("Mist!")
    #  return [distinv, d1]
    # else:
    #  lprint('True')
    if verbose:
        lprint('#I Number of distinguished involutions = ' + str(len(distinv)))
        lprint(' (' + str(zael) + ')\n')
    return [distinv, charvec, nvec] if nega else [distinv, charvec]


# F starorbitinv (for use in distinguishedinvolutions_eq and libdistinv)
def starorbitinv(W, pw, lcell=None):
    """returns the orbit  of a  distinguished involution  (among others,
    for use in 'libdistinv' and in 'cellrepstarorbit') under  N. Xi's
    'double' star operation;  this shows that,  if d is distinguished
    and the star operation is defined for d (with respect to s, t such
    that st has order 3),  then ((d^*)^{-1})^* is also distinguished;
    see Section 1.4 in

        N. Xi, The based ring of two-sided cells of affine Weyl groups
        of type $~A_{n-1}$. Mem. Amer. Math. Soc.,  vol. 157, no. 749,
        Providence, R.I., 2002.

    The optional  argument  'lcell' can be a  list of elements in the
    same left as the given element 'pw'; in this case, the star orbit
    of this list (see 'klstarorbit') is also returned  (with elements
    represented as 'coxelms').
    """
    orb = [pw[:]]
    n = len(W.rank)
    orb1 = set([pw[:n]])
    if lcell is not None:
        if isinstance(lcell[0], tuple) and len(lcell[0]) == n:
            ncell = [[bytes(W.coxelmtoperm(x)) for x in lcell]]
        elif isinstance(lcell[0], tuple) and len(lcell[0]) == 2 * W.N:
            ncell = [[bytes(x) for x in lcell]]
        else:
            ncell = [[bytes(W.wordtoperm(x)) for x in lcell]]
    for d in orb:
        for s in W.rank:
            for t in range(s):
                if W.coxetermat[s][t] == 3:
                    if (d[s] >= W.N and d[t] < W.N) or (d[s] < W.N and d[t] >= W.N):
                        d1 = leftklstar(W, perminverse(leftklstar(W, d, s, t)), s, t)
                        if not d1[:len(W.rank)] in orb1:
                            orb.append(d1)
                            orb1.add(d1[:len(W.rank)])
                            if lcell is not None:
                                ncell.append([bytes(x)
                                      for x in klstaroperation(W, s, t, ncell[orb.index(d)])])
                            # if W.permorder(d1)!=2:
                            #  print("Mist!")
                            #  return False
    if lcell is None:
        return orb
    return [orb, [[tuple(x[:len(W.rank)]) for x in l] for l in ncell]]


def starorbitinv1(W, distinv):
    """decomposes list of distinguished involutions into orbits
    under the star operation.
    """
    rest = [W.wordtoperm(w) for w in distinv]
    reps = []
    while rest != []:
        orb = starorbitinv(W, rest[0])
        for x in orb:
            rest.remove(x)
        l = W.permlength(orb[0])
        r = orb[0]
        for x in orb[1:]:
            lx = W.permlength(x)
            if lx < l:
                l = lx
                r = x
        reps.append([l, r])
        reps.sort(key=(lambda i: i[0]))
    return [i[1] for i in reps]


def starorbitinv2(W):
    """decomposes the list of involutions into orbits under the
    star operation.
    """
    rest = involutions(W)
    reps = []
    while rest != []:
        orb = starorbitinv(W, rest[0])
        for x in orb:
            rest.remove(x)
        l = [W.permlength(x) for x in orb]
        lmin, lmax = min(l), max(l)
        if lmin <= W.N - lmax:
            r = l.index(lmin)
        else:
            r = l.index(lmax)
        reps.append([orb[r], l[r]])
    reps.sort(key=(lambda i: i[1]))
    return [i[0] for i in reps]

# F distinguishedinvolutions_eq


def distinguishedinvolutions_eq(W, verbose=False):
    """similar to 'distinguishedinvolutions'  but this function only
    works in, and is optimised for, the case of equal parameters,
    where Lusztig's properties P1-P15  are known to hold  and  it
    makes sense to use  the  star operations,  especially N. Xi's
    double star operations  (see  'starorbitinv').  This function
    deals with type  H4 in 15s, with type E6 in 20s, with type E7
    in  180s and with type E8 in about 33 hours.

    See also 'distinguishedinvolutions' and 'libdistinv'.
    """
    v = lpol([1], 1, 'v')
    ct = chartable(W)
    w0 = longestperm(W)
    poin = poincarepol(W, v).coeffs
    lcl = [len(w) for w in conjugacyclasses(W)['reps']]
    maxn = sum([ct['irreducibles'][i][0] for i in range(len(ct['a']))
                if ct['a'][i] == ct['b'][i]])
    rest = involutions(W)
    repsinv = []
    if any(f % 2 == 1 for f in W.degrees):
        while rest:
            pw = rest[0]
            orb = starorbitinv(W, pw)
            for x in orb:
                rest.remove(x)
            l = [W.permlength(x) for x in orb]
            l1 = min(l)
            repsinv.append(orb[l.index(l1)])
    else:
        while rest:
            pw = rest[0]
            orb = starorbitinv(W, pw)
            for x in orb:
                rest.remove(x)
            l = [W.permlength(x) for x in orb]
            l1 = min(l)
            l2 = max(l)
            if l1 <= W.N - l2:
                repsinv.append(orb[l.index(l1)])
            else:
                repsinv.append(permmult(orb[l.index(l2)], w0))
    repsinv.sort(key=(lambda x: W.permlength(x)))
    maxl = W.permlength(repsinv[-1])
    if verbose:
        lprint('#I maximum length: ' + str(maxl) + ', ')
        lprint(' number of left cells: ' + str(maxn) + '\n')
    ti = heckechartable(W, v)['irreducibles']
    schur = schurelms(W, v)
    fshi = [s.coeffs[0] for s in schur]
    ainv = [-s.val // 2 for s in schur]
    tup = [[i, ainv[i]] for i in range(len(ainv))]
    tup.sort(key=(lambda i: i[1]), reverse=True)
    ti = [ti[tup[i][0]] for i in range(len(ainv))]
    fshi = [fshi[tup[i][0]] for i in range(len(ainv))]
    ainv = [ainv[tup[i][0]] for i in range(len(ainv))]
    chn = [ct['charnames'][tup[i][0]] for i in range(len(ainv))]
    ti1 = [ct['irreducibles'][tup[i][0]] for i in range(len(ainv))]
    signchar = [(-1)**lw for lw in lcl]
    signp = [ti1.index([l[j] * signchar[j] for j in range(len(lcl))]) for l in ti1]
    if W.N in lcl:
        iw0 = lcl.index(W.N)
        eps = [x[iw0] // x[0] for x in chartable(W)['irreducibles']]
        eps = [eps[tup[i][0]] for i in range(len(ainv))]
    distinv = [list(range(2 * W.N)), w0]
    charvec = [[[chn[ti1.index(len(ainv) * [1])], 1]],
             [[chn[ti1.index(signchar)], (-1)**W.N]]]
    cpmat = []
    cp = len(ainv) * [0]
    cp[0] = 1
    cpmat.append({bytes(W.rank): ';'.join(poltostr(f) for f in cp)})
    cps = {}
    if verbose:
        lprint('#I length  0 - 1 element, 1 class polynomial; 1 distinv\n')
    for l in range(maxl):
        if verbose:
            if l < 9:
                lprint('#I length  ' + str(l + 1))
            else:
                lprint('#I length ' + str(l + 1))
        nl = set()
        if l == 0:
            ol = []
        else:
            ol = set(cpmat[l - 1])
        for w in cpmat[l]:
            for s in W.permgens:
                nw = bytes([s[i] for i in w])
                if nw not in ol:
                    nl.add(nw)
            if len(nl) == poin[l + 1]:
                break
        cps = {}
        if verbose:
            lprint(' - ')
        ll = len(nl)
        spols = []
        while nl:
            w = W.coxelmtoword(next(iter(nl)))
            pw = W.wordtoperm(w)
            pw1 = perminverse(pw)
            t = testcyclicshift1(W, w, pw)
            if t[0] == 1:
                cp = len(ainv) * [0]
                cp[t[2]] = 1
            else:
                cp1 = [strtopol(f, 'v')
                       for f in cpmat[l - 1][bytes(t[2])].split(';')]
                cp2 = [strtopol(f, 'v') for f in cpmat[l][bytes([W.permgens[t[3]][i]
                                                        for i in t[2]])].split(';')]
                cp = [v * cp1[i] + (v - 1) * cp2[i] for i in range(len(ainv))]
            strcp = ';'.join(poltostr(f) for f in cp)
            ic = len(spols) - 1
            while ic >= 0:
                if strcp == spols[ic]:
                    break
                ic -= 1
            if ic == -1:
                spols.append(strcp)
            for x in t[1]:
                cx = x[:len(W.rank)]
                cps[bytes(cx)] = spols[ic]
                nl.remove(bytes(cx))
            if pw1 not in t[1]:
                for x in t[1]:
                    cx = perminverse(x)[:len(W.rank)]
                    cps[bytes(cx)] = spols[ic]
                    nl.remove(bytes(cx))
            if W.permorder(pw) == 2 and pw in repsinv and pw not in distinv:
                cpv = []
                for j in range(len(ainv)):
                    if isinstance(cp[j], int):
                        cpv.append(cp[j])
                    elif cp[j].coeffs == []:
                        cpv.append(0)
                    else:
                        cpv.append(cp[j].value(v**2))
                lc = []
                nonz = -1
                for i in range(len(ainv)):
                    if ainv[i] > len(w) or (nonz != -1 and nonz != ainv[i]):
                        lcc = 0
                    else:
                        lcc = zeroterm(v**(ainv[i] - len(w)) * sum(cpv[j] * ti[i][j]
                                          for j in range(len(ainv)) if cpv[j] != 0))
                        if nonz == -1 and lcc != 0:
                            nonz = ainv[i]
                    lc.append(lcc)
                ii = [i for i in range(len(ainv)) if lc[i] != 0]
                ftot = 1
                for i in ii:
                    ftot *= fshi[i]
                cof = []
                for i in ii:
                    cf = 1
                    for j in ii:
                        if i != j:
                            cf *= fshi[j]
                    cof.append(cf)
                nd = (-1)**len(w) * sum(cof[i] * lc[ii[i]] for i in range(len(ii)))
                if nd % ftot == 0:
                    nd = nd // ftot
                else:
                    print("Mist!")
                    return False
                # nd=(-1)**len(w)*sum((W.order*lc[i])//fshi[i]
                #                         for i in range(len(fshi)))//W.order
                if nd != 0:
                    sto = starorbitinv(W, pw)
                    distinv.extend(sto)
                    char = []
                    for i in range(len(ainv)):
                        if lc[i] != 0:
                            char.append([chn[i], lc[i]])
                        # if lc[i]>0:
                        #  char.append([chn[i], lc[i]])
                        # elif lc[i]<0:
                        #  char.append([chn[i], -lc[i]])
                    char = char[::-1]
                    for i in sto:
                        charvec.append(char)
                pw0 = permmult(pw, w0)
                if all(f % 2 == 0 for f in W.degrees) and pw0 not in distinv:
                    nd = sum(eps[ii[i]] * cof[i] * lc[ii[i]] for i in range(len(ii)))
                    if nd % ftot == 0:
                        nd = nd // ftot
                    else:
                        print("Mist!")
                        return False
                    if nd != 0:
                        sto0 = starorbitinv(W, pw0)
                        distinv.extend(sto0)
                        char0 = []
                        for i in range(len(ainv)):
                            if lc[i] != 0:
                                char0.append(
                                    [signp[i], (-1)**(W.N + len(w)) * eps[i] * lc[i]])
                            # if lc[i]>0:
                            #  char0.append([signp[i], lc[i]])
                            # elif lc[i]<0:
                            #  char0.append([signp[i], -lc[i]])
                        char0.sort(key=(lambda i: i[0]), reverse=True)
                        char0 = [[chn[i[0]], i[1]] for i in char0]
                        for i in sto0:
                            charvec.append(char0)
        if verbose:
            lprint(str(ll) + ' elements, ' + str(len(spols)) + ' class polynomials; ')
            lprint(str(len(distinv)) + ' distinvs\n')
        if l > 0:
            cpmat[l - 1] = 0
        cpmat.append(cps)
        if len(distinv) == maxn:
            break
    res = [[W.permtoword(distinv[i]), charvec[i]] for i in range(len(distinv))]
    res.sort(key=(lambda x: len(x[0])))
    # d1=distinguishedinvolutions(W, poids)
    # d1=libdistinv(W, 1)
    # if not (len(distinv)==len(d1) and all(i in d1 for i in distinv)):
    #  print("Grosser Mist!")
    #  return [distinv, d1]
    # else:
    #  lprint('True')
    if verbose:
        lprint('#I Number of distinguished involutions = ' + str(len(res)) + '\n')
    return [list(l) for l in zip(*res)]


def allcellsleadingcoeffs(W, weightL, v, newnorm=False, verbose=False):
    """returns a list which contains the pairwise different results of
    'leftcellleadingcoeffs' as we run over all left cells of W with
    at least two irreducible components.

    >>> allcellsleadingcoeffs(coxeter("H", 3), 1, v)
    [[[[("3_s'",), 1, ir5], [("overline{3}_s'",), 1, 1-ir5]],
      [[('3_s',), ir5, 1], [('overline{3}_s',), 1-ir5, 1]],
      [[("4_r'",), 1, -1], [('4_r',), 1, 1]]],
     [[[], 1],         # all distinguished involutions with signs
      [[0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2], 1],
      [[2, 1, 0, 1, 0, 2, 1, 0, 1, 2], 1],
      [[0, 1, 0, 1, 0], 1],
      [[1, 0, 2, 1], 1],
      [[0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0], 1],
      [[1, 0, 2, 1, 0, 1, 0, 2, 1], 1],
      [[0, 1, 0, 2, 1, 0], 1],
      [[2], 1],
      [[0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1], 1],
      [[1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2], 1],
      [[0], 1], [[1, 2, 1], 1],
      [[0, 1, 0, 1, 2, 1, 0, 1, 0], 1], [[1, 0, 1, 2, 1, 0, 1], 1]],
     [("5_r'",), ("3_s'",), ("1_r'",), ('3_s',), # special characters
      ('1_r',), ('5_r',), ("4_r'",)]]

    >>> allcellsleadingcoeffs(coxeter("B", 3), [2, 1, 1], v)
    [[[[('[[1, 1], [1]]',), 1,  1],
       [('[[1], [2]]',),    1, -1]],
      [[('[[1], [2]]',), 1, -1],
       [('[[], [3]]',),  1,  1]],
      [[('[[1, 1, 1], []]',), 1, -1],
       [('[[1, 1], [1]]',),   1,  1]]],
      [[[], 1],
       [[0], 1],
       [[1], 1],
       [[2], 1],
       [[1, 0, 1], 1],
       [[0, 2], 1],
       [[0, 1, 0], -1],
       [[2, 1, 0, 1, 2], 1],
       [[1, 0, 2, 1], 1],
       [[1, 2, 1], 1],
       [[0, 1, 0, 1], 1],
       [[0, 2, 1, 0, 1, 2], 1],
       [[1, 0, 1, 2, 1, 0, 1, 2], 1],
       [[0, 1, 0, 2, 1, 0, 1, 2], -1],
       [[0, 1, 0, 1, 2, 1, 0, 1], -1],
       [[0, 1, 0, 1, 2, 1, 0, 1, 2], 1]]
      [('[[1], [2]]',), ('[[1], [1, 1]]',), ('[[1, 1, 1], []]',),
       ('[[2], [1]]',), ('[[], [2, 1]]',), ('[[], [1, 1, 1]]',),
       ('[[3], []]',), ('[[2, 1], []]',)]]

    See also 'klcells' and 'leftcellleadingcoeffs'.
    """
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL[:]
    if all(p == 1 for p in poids):
        kl = [c.X for c in klcells(W, poids, v, allcells=False)[1]]
    else:
        kl = [c.X for c in klcellsun(W, poids, v)]
    cp = allclasspolynomials(W, [v**(2 * i) for i in poids])
    ch = chartable(W, chars=False)['charnames']
    nlc, dlc = [], []
    slc = set()
    if verbose:
        lprint('#I ')
    for l1 in kl:
        l = leftcellleadingcoeffs(W, poids, v, l1, clpols=cp, newnorm=newnorm)
        if verbose:
            lprint(str(l['nd']))
        dlc.append([l['distinv'], l['nd']])
        slc.add(ch.index(l['special']))
        if len(l['ti']) > 1:
            tl = transposemat([flatlist(i) for i in l['ti']])
            ok = True
            for m in nlc:
                if len(m) == len(tl) and all(m.count(r) == tl.count(r) for r in m):
                    ok = False
            if ok:
                nlc.append(tl)
    if verbose:
        lprint('\n')
    slc = list(slc)
    slc.sort()
    slc = [ch[i] for i in slc]
    for l in nlc:
        if len([1 for i in l[0] if i in slc]) != 1:
            print('multiple special in cell')
            return l
    return [[transposemat(l) for l in nlc], dlc, slc]


def libdistinv(W, weightL, unpack=True):
    r"""returns a pre-computed and explicitly stored list  of distinguished
    involutions.  Among other properties, these elements  form a set of
    representatives for the left cells of W  with respect  to the given
    weight function.  This function only works  for  W of  type I_2(m),
    F_4  (any weight  function)  and H_3,  H_4,  E_6,  E_7,  E8  (equal
    parameters) and only if all the weights are strictly positive.

    One  can reproduce these data  using 'distinguishedinvolutions' but
    this will take some time.  Also,  some further arguments are needed
    to deal with all choices of unequal parameters for  I_2(m) and F_4.
    Here, we rely on the results and techniques in::

        M. Geck, Computing Kazhdan-Lusztig cells for unequal parameters,
        J. Algebra 281 (2004), 342--365.

    For the  large groups of  exceptional type,  we only store a set of
    representatives under N. Xi's 'double'  star operation;  this shows
    that, if d is distinguished and the star operation is defined for d
    (with respect to generators s, t such that st has order 3), then the
    element ((d^*)^{-1})^* is also distinguished; see Section 1.4 in::

        N. Xi, The based ring of two-sided cells of affine Weyl groups
        of type $~A_{n-1}$. Mem. Amer. Math. Soc.,  vol. 157, no. 749,
        Providence, R.I., 2002.

    It will take a couple of minutes or so to unpack  these data.  For
    example, in  type E8  there are  101796  distinguished involutions
    but  only  106  orbits  under  the  'double' star  operation.  The
    'unpacking' is done by the function 'starorbitinv'.

    >>> W = coxeter("E", 8);
    >>> d=timer(libdistinv, W, 1)   # not tested
    188.06
    >>> len(d)   # not tested
    101796

    See also 'distinguishedinvolutions' and 'distinva'.
    """
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL[:]
    if len(W.cartantype) > 1:
        raise ValueError('Sorry, only irreducible W of exceptional type')
    if all(p == 0 for p in poids):
        return [[]]
    typ = W.cartantype[0][0]
    rk = list(W.cartantype[0][1])
    if typ == 'H' and rk == [0, 1, 2]:
        l = ['', '0', '1', '2', '02', '121', '1021', '01010', '01210', '010210',
           '1012101', '0210102', '10102101', '010121010', '102101021',
           '2101021012', '01021010210', '1010210102101', '01010210102101',
           '01012101021012', '10102101021012', '010102101021012']
        chrs0 = ['1.1', '7.1c6.1', '7.1c6.1', '7.1c6.1', '3.1', '9.1c8.1', '3.1',
               '2.1', '9.1c8.1', '3.1', '9.1c8.1', '2.1', '3.1', '9.1c8.1', '2.1',
               '3.1', '2.1', '2.1', '5.1c4.1', '5.1c4.1', '5.1c4.1', '0.1']
        ch = chartable(W, chars=False)['charnames']
        chars = [[[ch[int(k.split('.')[0])], int(k.split('.')[1])]
                  for k in i.split('c')] for i in chrs0]
        if unpack:
            return [[int(s) for s in i] for i in l]
        else:
            return [[[int(s) for s in l[i]], chars[i]] for i in range(len(l))]
    elif typ == 'H' and rk == [0, 1, 2, 3]:
        l = ['', '0', '1', '2', '3', '02', '03', '13', '121', '232', '1021',
           '0232', '2132', '01010', '01210', '12321', '010210', '010103',
           '102321', '121321', '1012101', '0210102', '0123210', '10102101',
           '02101032', '12101321', '01023210', '01213210', '010121010',
           '102101021', '101232101', '032101023', '2101021012', '1021010321',
           '0121013210', '1010232101', '1012132101', '0232101023', '01021010210',
           '01012321010', '21012321012', '10321010213', '010210103210',
           '101210132101', '010121321010', '121012321012', '210102321012',
           '102321010213', '321010210123', '1010210102101', '0210123210102',
           '0103210102103', '2103210102132', '01010210102101', '01012101021012',
           '10102101021012', '10102101032101', '01012101321010',
           '12101021321012', '01210123210102', '01023210102103',
           '23210102101232', '010102101021012', '102101232101021',
           '101032101021013', '021032101021032', '0121010213210102',
           '1012101232101021', '1010232101021013', '0101321010210123',
           '1010321010210123', '1232101021012321', '01021012321010210',
           '10210321010210321', '01010321010210123', '21010321010210132',
           '101210102132101021', '010121012321010210', '210102321010210132',
           '210103210102101232', '012321010210123210', '1010210123210102101',
           '1210103210102101321', '0102103210102103210', '0210103210102101232',
           '01012101021321010210', '10123210102101232101',
           '210102101232101021012', '012101032101021013210',
           '102101032101021012321', '101021032101021032101',
           '2101232101021012321012', '0101232101021012321010',
           '21010210321010210321012', '01021010321010210123210',
           '10121010321010210132101', '32101021012321010210123',
           '021012321010210123210102', '1010210103210102101232101',
           '1210102103210102101321012', '0101210103210102101321010',
           '2321010210123210102101232', '01010210102101232101021012',
           '10210123210102101232101021', '121010210132101021012321012',
           '012101021032101021013210102', '010102101032101021012321010',
           '123210102101232101021012321', '0102101232101021012321010210',
           '0101032101021012321010210123', '01210102101321010210123210102',
           '10121010210321010210132101021', '01232101021012321010210123210',
           '12132101021013210102103210123', '101021012321010210123210102101',
           '021010321010210123210102101232', '0101210102103210102101321010210',
           '1012101021013210102101232101021', '1012321010210123210102101232101',
           '0121321010210123210102103210123', '21010210123210102101232101021012',
           '10210103210102101232101021012321',
           '010121010210132101021012321010210',
           '210123210102101232101021012321012',
           '010123210102101232101021012321010',
           '101213210102101232101021013210123',
           '0101021010210123210102101321010210',
           '0102101032101021012321010210123210',
           '3210102101232101021012321010210123',
           '01010210102101321010210123210102101',
           '12101232101021012321010210123210123',
           '02101232101021012321010210123210102',
           '01012132101021012321010210132101023',
           '101021010321010210123210102101232101',
           '010102321010210123210102101321010213',
           '0101021321010210123210102101321010213',
           '0121012321010210123210102101232101023',
           '1021012321010210123210102101232101021',
           '12101021013210102101232101021012321012',
           '01010210103210102101232101021012321010',
           '02101023210102101232101021013210102132',
           '021010213210102101232101021013210102132',
           '101210123210102101232101021012321010213',
           '010210123210102101232101021012321010210',
           '0121010210132101021012321010210123210102',
           '1021010232101021012321010210123210102132',
           '1210321010210123210102101232101021012321',
           '10210102132101021012321010210123210102132',
           '10102101232101021012321010210123210102101',
           '01012101232101021012321010210123210102103',
           '101210102101321010210123210102101232101021',
           '010210102321010210123210102101232101021032',
           '012103210102101232101021012321010210123210',
           '0102101021321010210123210102101232101021032',
           '0101021012321010210123210102101232101021013',
           '2101021012321010210123210102101232101021012',
           '01012101021013210102101232101021012321010210',
           '10102101023210102101232101021012321010210321',
           '10121032101021012321010210123210102101232101',
           '021010210123210102101232101021012321010210132',
           '101021010213210102101232101021012321010210321',
           '321010210123210102101232101021012321010210123',
           '0101021010210132101021012321010210123210102101',
           '0101021010232101021012321010210123210102103210',
           '1210102101232101021012321010210123210102101321',
           '0101210321010210123210102101232101021012321010',
           '1210102321010210123210102101232101021012321012',
           '01010210102132101021012321010210123210102103210',
           '10210102101232101021012321010210123210102101321',
           '02321010210123210102101232101021012321010210123',
           '010102101021012321010210123210102101232101021012',
           '012101021012321010210123210102101232101021013210',
           '010102101321010210123210102101232101021012321010',
           '012101023210102101232101021012321010210123210102',
           '121321010210123210102101232101021012321010210123',
           '0102101021012321010210123210102101232101021013210',
           '1021321010210123210102101232101021012321010210123',
           '10121010210123210102101232101021012321010210132101',
           '02101021013210102101232101021012321010210123210102',
           '10121010232101021012321010210123210102101232101021',
           '01010321010210123210102101232101021012321010210123',
           '01210321010210123210102101232101021012321010210123',
           '101021010210123210102101232101021012321010210132101',
           '010210321010210123210102101232101021012321010210123',
           '0101021010210132101021012321010210123210102101321010',
           '0101210102101232101021012321010210123210102101321010',
           '1021010210132101021012321010210123210102101232101021',
           '0101210102321010210123210102101232101021012321010210',
           '1012101321010210123210102101232101021012321010210123',
           '0210102321010210123210102101232101021012321010210123',
           '10102101321010210123210102101232101021012321010210123',
           '010210102101321010210123210102101232101021012321010210',
           '010121010321010210123210102101232101021012321010210123',
           '102101021321010210123210102101232101021012321010210123',
           '2101021012321010210123210102101232101021012321010210123',
           '01010210102103210102101232101021012321010210123210102101',
           '10102101021013210102101232101021012321010210123210102101',
           '01021010210321010210123210102101232101021012321010210123',
           '0101210102101232101021012321010210123210102101232101021012',
           '1010210102101232101021012321010210123210102101232101021012',
           '1010210102101321010210123210102101232101021012321010210123',
           '01010210102101232101021012321010210123210102101232101021012',
           '01010210102101321010210123210102101232101021012321010210123',
           '01012101021012321010210123210102101232101021012321010210123',
           '10102101021012321010210123210102101232101021012321010210123',
           '010102101021012321010210123210102101232101021012321010210123']
        chrs0 = ['0.1', '4.1c2.1', '4.1c2.1', '4.1c2.1', '4.1c2.1', '12.1c10.1',
               '12.1c10.1', '12.1c10.1', '19.1c17.1', '19.1c17.1', '12.1c10.1',
               '26.1', '12.1c10.1', '30.1', '19.1c17.1', '19.1c17.1', '12.1c10.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '26.1', '33.2c32.1c29.1c28.1c25.1c24.1c23.1c22.1c21.1c9.1c8.1',
               '19.1c17.1', '30.1', '19.1c17.1', '12.1c10.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '26.1', '26.1',
               '33.2c32.1c29.1c28.1c25.1c24.1c23.1c22.1c21.1c9.1c8.1',
               '19.1c17.1', '30.1', '19.1c17.1', '30.1', '12.1c10.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '26.1', '26.1',
               '33.2c32.1c29.1c28.1c25.1c24.1c23.1c22.1c21.1c9.1c8.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '30.1', '19.1c17.1', '19.1c17.1', '30.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '26.1', '33.2c32.1c29.1c28.1c25.1c24.1c23.1c22.1c21.1c9.1c8.1',
               '33.2c32.1c29.1c28.1c25.1c24.1c23.1c22.1c21.1c9.1c8.1', '26.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '12.1c10.1', '30.1', '19.1c17.1', '30.1', '30.1',
               '33.2c32.2c29.2c28.2c25.1c24.1c23.1c22.1c16.1c15.1c7.1c6.1',
               '33.2c32.2c29.2c28.2c25.1c24.1c23.1c22.1c16.1c15.1c7.1c6.1',
               '33.2c32.2c29.2c28.2c25.1c24.1c23.1c22.1c16.1c15.1c7.1c6.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '26.1', '26.1',
               '33.2c32.1c29.1c28.1c25.1c24.1c23.1c22.1c21.1c9.1c8.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '26.1', '31.1', '19.1c17.1', '30.1', '30.1', '26.1',
               '33.2c32.1c29.1c28.1c25.1c24.1c23.1c22.1c21.1c9.1c8.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '33.2c32.2c29.2c28.2c25.1c24.1c23.1c22.1c16.1c15.1c7.1c6.1',
               '33.2c32.2c29.2c28.2c25.1c24.1c23.1c22.1c16.1c15.1c7.1c6.1',
               '26.1', '19.1c17.1', '30.1', '31.1', '30.1', '26.1',
               '33.2c32.1c29.1c28.1c25.1c24.1c23.1c22.1c21.1c9.1c8.1',
               '33.2c32.2c29.1c28.1c25.1c24.1c23.1c22.1c21.1c16.1c15.1c14.1',
               '33.2c32.2c29.2c28.2c25.1c24.1c23.1c22.1c16.1c15.1c7.1c6.1',
               '26.1', '19.1c17.1', '30.1', '30.1', '31.1', '26.1', '26.1',
               '19.1c17.1', '30.1', '31.1', '30.1', '26.1', '26.1', '30.1',
               '31.1', '30.1', '19.1c17.1', '26.1', '31.1', '30.1', '30.1',
               '30.1', '27.1', '26.1', '31.1', '30.1', '31.1', '30.1', '26.1',
               '27.1', '31.1', '30.1', '30.1', '31.1', '26.1', '27.1', '30.1',
               '31.1', '30.1', '31.1', '26.1', '27.1', '31.1', '30.1', '30.1',
               '31.1', '20.1c18.1', '27.1', '26.1', '31.1', '31.1', '30.1',
               '31.1', '27.1', '20.1c18.1', '31.1', '31.1', '30.1', '27.1',
               '27.1', '20.1c18.1', '31.1', '31.1', '30.1', '27.1', '20.1c18.1',
               '27.1', '31.1', '30.1', '31.1', '27.1', '20.1c18.1', '27.1',
               '31.1', '31.1', '30.1', '27.1', '20.1c18.1', '27.1', '31.1',
               '31.1', '30.1', '27.1', '20.1c18.1', '20.1c18.1', '27.1', '27.1',
               '31.1', '31.1', '31.1', '13.1c11.1', '20.1c18.1', '27.1', '27.1',
               '20.1c18.1', '31.1', '31.1', '20.1c18.1', '27.1', '27.1',
               '13.1c11.1', '20.1c18.1', '31.1', '31.1', '20.1c18.1',
               '20.1c18.1', '27.1', '27.1', '20.1c18.1', '13.1c11.1', '31.1',
               '27.1', '20.1c18.1', '13.1c11.1', '31.1', '13.1c11.1', '27.1',
               '13.1c11.1', '13.1c11.1', '13.1c11.1', '13.1c11.1', '5.1c3.1',
               '5.1c3.1', '5.1c3.1', '5.1c3.1', '1.1']
        ch = chartable(W, chars=False)['charnames']
        chars = [[[ch[int(k.split('.')[0])], int(k.split('.')[1])]
                  for k in i.split('c')] for i in chrs0]
        if unpack:
            return [[int(s) for s in i] for i in l]
        else:
            return [[[int(s) for s in l[i]], chars[i]] for i in range(len(l))]
    elif typ == 'F' and rk == [0, 1, 2, 3]:
        l1111 = ['', '0', '1', '2', '3', '02', '03', '13', '010', '232', '1021',
           '1212', '0103', '0232', '2132', '02102', '12321', '012102',
           '210212', '021032', '102321', '121321', '132123', '1021021',
           '0123210', '2123212', '0321023', '01021021', '10210321',
           '01213210', '21023212', '21232123', '01321023', '32102123',
           '010210212', '121232123', '021232102', '103210213', '01212321023',
           '10212321021', '21032102132', '01032102123', '2102123210212',
           '0102123210213', '0210321021232', '1210321021321',
           '021021232102132', '012103210213210', '102103210212321',
           '321021232102123', '0102102123210212', '1210232102123212',
           '10210212321021321', '01021032102123210', '12102132102123212',
           '02321021232102123', '012102321021232102', '010321021232102123',
           '0102102123210213210', '0121021321021232102', '1021321021232102123',
           '1212321021232102123', '01021023210212321021', '02102321021232102123',
           '010210213210212321021', '010210321021232102123',
           '012102321021232102123', '210212321021232102123',
           '0121021232102123210212', '1021021232102123210212',
           '1021021321021232102123', '010210212321021232102123']
        l1122 = ['', '0', '1', '2', '3', '02', '03', '13', '010', '121', '212',
           '232', '1021', '1212', '0103', '0232', '2132', '01210', '12321',
           '32123', '012102', '021032', '102321', '121321', '132123', '232123',
           '0123210', '2123212', '01021021', '01210212', '10210212', '10210321',
           '01023210', '01213210', '12123212', '21023212', '12132123', '21232123',
           '01321023', '010210212', '121232123', '021232102', '0102103210',
           '0121232102', '0210232102', '0121321023', '0212321023', '0103210213',
           '0132102123', '1032102123', '01212321023', '10212321021',
           '01032102123', '010212321021', '102102321021', '102123210213',
           '021032102132', '2102123210212', '0102123210213', '0210321021232',
           '21021232102132', '10210321021321', '21232102123212',
           '021021232102132', '102103210212321', '321021232102123',
           '1210212321021321', '0102103210213210', '0212321021232102',
           '2321021232102123', '10210212321021321', '01021032102123210',
           '12102132102123212', '02321021232102123', '012102123210213210',
           '102123210212321021', '121321021232102123', '212321021232102123',
           '0102102123210213210', '0121021321021232102', '1021321021232102123',
           '1212321021232102123', '21021232102123210212', '01210321021232102123',
           '010210213210212321021', '010210321021232102123',
           '012102321021232102123', '01021021232102123210212',
           '01021021321021232102123', '01210212321021232102123',
           '10210212321021232102123', '010210212321021232102123']
        l1133 = ['', '0', '1', '2', '3', '02', '03', '13', '010', '121', '212',
           '232', '1021', '1212', '0103', '0232', '2132', '01210', '02102',
           '12321', '32123', '010210', '012102', '210212', '021032', '102321',
           '121321', '132123', '232123', '1021021', '0123210', '2123212',
           '0321023', '01021021', '01210212', '10210212', '10210321', '01023210',
           '01213210', '12123212', '21023212', '12132123', '21232123',
           '01321023', '32102123', '010210212', '121232123', '021232102',
           '103210213', '0102103210', '0121232102', '0210232102', '0121321023',
           '0212321023', '0103210213', '0132102123', '1032102123', '01212321023',
           '10212321021', '21032102132', '01032102123', '010212321021',
           '102102321021', '102123210213', '021032102132', '2102123210212',
           '0102123210213', '0210321021232', '1210321021321', '21021232102132',
           '10210321021321', '21232102123212', '021021232102132',
           '012103210213210', '102103210212321', '321021232102123',
           '0102102123210212', '1210212321021321', '0102103210213210',
           '1210232102123212', '0212321021232102', '2321021232102123',
           '10210212321021321', '01021032102123210', '12102132102123212',
           '02321021232102123', '012102123210213210', '012102321021232102',
           '102123210212321021', '010321021232102123', '121321021232102123',
           '212321021232102123', '0102102123210213210', '0121021321021232102',
           '1021321021232102123', '1212321021232102123', '01021023210212321021',
           '21021232102123210212', '01210321021232102123',
           '02102321021232102123', '010210213210212321021',
           '010210321021232102123', '012102321021232102123',
           '210212321021232102123', '0121021232102123210212',
           '1021021232102123210212', '1021021321021232102123',
           '01021021232102123210212', '01021021321021232102123',
           '01210212321021232102123', '10210212321021232102123',
           '010210212321021232102123']
        if poids[0] == poids[2]:
            return [[int(s) for s in i] for i in l1111]
        elif poids[0] > 0 and poids[2] > poids[0]:
            if poids[2] == 2 * poids[0]:
                return [[int(s) for s in i] for i in l1122]
            else:
                return [[int(s) for s in i] for i in l1133]
        elif poids[2] > 0 and poids[0] > poids[2]:
            J = [3, 2, 1, 0]
            W = coxeter("F", 4)
            if poids[0] == 2 * poids[2]:
                return [W.reducedword([J[int(s)] for s in i], W) for i in l1122]
            else:
                return [W.reducedword([J[int(s)] for s in i], W) for i in l1133]
        else:
            raise NotImplementedError('Sorry, not yet implemented')
    elif typ[0] == 'E' and rk == [0, 1, 2, 3, 4, 5]:
        reps = ['', '3', '12', '015', '232', '1315', '01454', '020454', '020320',
              '0131431', '0120454', '1314315431', '23123431234', '01203120325',
              '123123431234', '020320432054320', '02031203431203243',
              '01203120324312032431', '020312043120324315431203243',
              '0120312032431203243154312032431',
              '012031203243120324315431203243154320']
        chrs0 = ['0.1', '3.1', '10.1', '14.1c8.1', '14.1c6.1', '21.1', '19.1',
               '12.1', '23.1', '18.1c17.1c16.1', '17.1c16.1c2.1', '24.1',
               '18.2c17.1c5.1', '20.1', '13.1', '15.1c9.1', '22.1', '11.1',
               '15.1c7.1', '4.1', '1.1']
        ch = chartable(W, chars=False)['charnames']
        chars = [[[ch[int(k.split('.')[0])], int(k.split('.')[1])]
                  for k in l.split('c')] for l in chrs0]
        if unpack:
            f = [W.permtoword(x) for x in flatlist([starorbitinv(W,
                     W.wordtoperm([int(i) for i in r])) for r in reps])]
            f.sort(key=(lambda x: len(x)))
        else:
            f = [[[int(i) for i in reps[r]], chars[r]] for r in range(len(reps))]
        return f
    elif typ[0] == 'E' and rk == [0, 1, 2, 3, 4, 5, 6]:
        reps = ['', '2', '12', '020', '124', '146', '0120', '1246', '01204',
              '020320', '020454', '012046', '0131431', '0120454', '1314316',
              '01314316', '020320565', '0120312032', '0120454654',
              '12312343123', '01203120325', '123123431234', '123123431236',
              '1231234312346', '0120312032565', '020320432054320',
              '231243123565432', '131431543165431', '123431235654312',
              '0131431543165431', '01203120324312032', '01203435436543120',
              '012031203243120326', '01203120324312032431',
              '12312343543126543123', '012031203243120324316',
              '020320432054320654320', '123120343120543126543123',
              '232432543123456543123456', '020312043120324315431203243',
              '1234312032543654312032431546', '12312343123454312345654312345',
              '123123431234543123456543123456',
              '0120312032431203243154312032431',
              '0120343254312036543120324315465',
              '0131431543120654312032431543654',
              '0203204320543120345654312032435465',
              '012031203243120324315431203243154320',
              '123123431234543120324315432654312345',
              '123123431203243543265431203243154326',
              '02032043120543120326543120324315432065432',
              '123120324312032431543123456543120324315432',
              '123123431203243154312032431543206543120324315432',
              '01203120324312032431543120324315432065431203243154320',
              '01203120324312032431543120324315432065431203243154320654312345',
              '012031203243120324315431203243154320654312032431543206543123456']
        chrs0 = ['0.1', '3.1', '10.1', '17.1c6.1', '17.1c14.1', '9.1',
               '28.1c23.1', '28.1c5.1', '35.1', '38.1', '30.1', '24.1',
               '49.1c46.1c45.1', '49.1c46.1c19.1', '37.1', '54.1c43.1', '53.1',
               '56.1c51.1', '40.1', '49.1c45.2c13.1', '59.1c58.1', '26.1',
               '54.1c32.1', '57.1c21.1', '41.1', '55.1c42.1', '53.1', '27.1',
               '35.1', '48.1c47.1c18.1', '57.1c50.1', '59.1c58.1', '52.1',
               '36.1', '56.1c20.1', '31.1', '25.1', '40.1', '48.1c47.1c44.1',
               '55.1c33.1', '24.1', '39.1', '16.1c15.1', '29.1c22.1', '41.1',
               '25.1', '34.1', '8.1', '34.1', '52.1', '29.1c4.1',
               '48.1c44.2c12.1', '16.1c7.1', '11.1', '2.1', '1.1']
        ch = chartable(W, chars=False)['charnames']
        chars = [[[ch[int(k.split('.')[0])], int(k.split('.')[1])]
                  for k in l.split('c')] for l in chrs0]
        if unpack:
            f = [W.permtoword(x) for x in flatlist([starorbitinv(W,
                     W.wordtoperm([int(i) for i in r])) for r in reps])]
            f.sort(key=(lambda x: len(x)))
        else:
            f = [[[int(i) for i in reps[r]], chars[r]] for r in range(len(reps))]
        return f
    elif typ[0] == 'E' and rk == [0, 1, 2, 3, 4, 5, 6, 7]:
        reps = ['', '7', '12', '020', '146', '0205', '1246', '14547', '232432',
              '020454', '012046', '0204547', '0565765', '01204676', '12454654',
              '131431676', '0120454654', '2324325432', '04546547654',
              '23123431234', '124546547654', '131234312346', '123123431234',
              '123123565765', '1231234312346', '0204546547654', '12312343123676',
              '01204546547654', '231243123565432', '343543654376543',
              '123123431234676', '123431235654312', '0120312032565765',
              '0131431543165431', '13143123454312345', '01203435436543120',
              '012031203243120326', '01203120324312032676',
              '01203120324312032431', '12312343543126543123',
              '232432543265432765432', '012031203243120324316',
              '0131431543165431765431', '13124312354312346765431',
              '12343123543123467654312', '01203120324312032431676',
              '131431543123456543123456', '124543206543120324315465',
              '123120343120324354312032431', '012034312354312034676543120',
              '1312043120324543120324315437', '0131234312032435657654312034',
              '1234312032543654312032431546', '0203204320543206543207654320',
              '12312343123454312345654312345', '123123431234543123456543123456',
              '123123431234546543123765431234',
              '1231203431203243543120324315432',
              '0131431543120654312032431543654',
              '0120343254312036543120324315465',
              '01203120324312032431543120324317',
              '13143154316543123456765431234567',
              '0203204320543120345654312032435465',
              '0131431543165431234567654312034567',
              '012031203243120324315431203243154320',
              '123123431234543120324315432654312345',
              '123120345431203243654312032431543265',
              '012034312354312032431546765431203245',
              '0120312032431203243154312032431543207',
              '232431234543123456543123456765431234567',
              '02032043120543120326543120324315432065432',
              '12312034543654312034765431203243154326576',
              '123123431234543123456543123456765431234567',
              '123120324312032431543123456543120324315432',
              '0203204312054312032654312032431543207654320',
              '013143125431236543120324315432065432765431203456',
              '123123431203243154312032431543206543120324315432',
              '020320431203254312032431654312032431543207654320',
              '123123431203454312032435465432076543120324315432',
              '2312431235431234654312032431543206543176543123456',
              '0131234312032435436543120347654312032431543206543176',
              '01203120324312032431543120324315432065431203243154320',
              '02032043205431206543120327654312032431543206543276543',
              '012031203243120324315431236543123476543120324315432067',
              '012034354312032431654312032431543206543176543120324315465',
              '0120312032431203243154312032431565431234765431203243154320',
              '0131431235431234654312032435467654312032431543206543176543',
              '02031203243120324315431203243154320654312032431543206543123456',
              '012031203243120324315431203243154320654312032431543206543123456',
              '123120343120324354312032431543265431234576543120324315432654317',
              '1231203431203243543120324315432654312345676543120324315432654317',
              '12312343123454312032431565431203243154320654327654312032431543' +
                '265431',
              '12312343120324354312365431203243154676543120324315432065431237' +
                '6543123',
              '12312343120345431203243546543120324315432065431234576543120324' +
                '31543265431',
              '01203120324312032431543120324315432065431234567654312032431543' +
                '206543123457',
              '02032043205431203265431203243156765431203243154320654312345676' +
                '54312032435465',
              '12312343123454312345654312032431543206765431203243154320654312' +
                '345676543123456',
              '01203120324312032431543120324316543120324315432654317654312032' +
                '4315432065431234',
              '12312034312032435431203243154326543120324315432065431234576543' +
                '12032431543265431',
              '01203120324312032431543120324315432065431203243154326543176543' +
                '1203243154320654312345',
              '12312032431203243154312032431543206543120324315432076543120324' +
                '315432065431234576543120324315432',
              '12312343123454312032431565431203243154320654327654312032431543' +
                '2065431234567654312032431543265431',
              '12312343120324315431203243154320654312032431543206543123456765' +
                '43120324315432065431234576543120324315432',
              '01203120324312032431543120324315432065431203243154320654312345' +
                '6765431203243154320654312345765431203243154320',
              '01203120324312032431543120324315432065431203243154320654312345' +
                '676543120324315432065431234567654312032431543206543123456',
              '01203120324312032431543120324315432065431203243154320654312345' +
                '6765431203243154320654312345676543120324315432065431234567']
        chrs0 = ['0.1', '67.1', '4.1', '71.1c2.1', '71.1c9.1', '73.1c14.1',
               '14.1c7.1', '80.1', '23.1', '28.1c17.1', '76.1c28.1',
               '92.1c78.1c39.1', '92.1c85.1c39.1', '42.1c36.1c12.1',
               '44.1c42.1c36.1', '99.1', '90.1c50.1', '88.1c53.1', '104.1c61.1',
               '92.1c85.2c69.1', '101.1c63.1', '44.2c42.1c19.1', '21.1',
               '63.1c31.1', '96.1c26.1', '108.1', '83.1c50.1', '56.1', '99.1',
               '110.1c59.1', '106.1', '80.1',
               '103.1c87.1c82.1c52.1c49.1c46.1c16.1',
               '103.2c98.1c87.1c58.1c55.1c52.1c49.1c46.1c41.1', '96.1c47.1',
               '104.1c61.1', '65.1', '103.1c98.1c82.1c58.1c52.1c49.1c46.1c25.1',
               '38.1', '53.1c34.1', '107.1', '111.1c60.1', '57.1', '106.1',
               '99.1', '109.1', '103.2c98.2c58.2c55.2c52.1c49.1c41.1c33.1c30.1',
               '90.1c50.1', '110.1c94.1', '99.1',
               '103.1c98.2c75.1c58.2c55.1c52.1c46.1c33.1c25.1', '101.1c63.1',
               '76.1c28.1', '91.1c51.1', '111.1c95.1', '54.1c35.1',
               '103.1c98.1c82.1c58.1c55.1c52.1c49.2c30.1c11.1', '97.1c48.1',
               '107.1', '108.1', '105.1c62.1', '102.1c64.1', '66.1',
               '102.1c64.1', '22.1', '66.1', '65.1', '90.1c50.1',
               '93.1c79.1c40.1', '100.1', '97.1c27.1', '108.1', '77.1c29.1',
               '103.1c98.2c75.1c58.3c55.3c52.1c33.3c30.2c6.1', '109.1', '57.1',
               '89.1c54.1', '105.1c62.1', '91.1c51.1', '109.1', '56.1',
               '93.1c86.1c40.1', '100.1', '64.1c32.1', '106.1', '84.1c51.1',
               '91.1c51.1', '24.1', '72.1c10.1', '100.1', '77.1c29.1',
               '45.1c43.1c37.1', '107.1', '100.1', '29.1c18.1', '43.1c37.1c13.1',
               '81.1', '45.2c43.1c20.1', '81.1', '74.1c15.1', '93.1c86.2c70.1',
               '15.1c8.1', '72.1c3.1', '5.1', '68.1', '1.1']
        ch = chartable(W, chars=False)['charnames']
        chars = [[[ch[int(k.split('.')[0])], int(k.split('.')[1])]
                  for k in l.split('c')] for l in chrs0]
        if unpack:
            f = [W.permtoword(x) for x in flatlist([starorbitinv(W,
                     W.wordtoperm([int(i) for i in r])) for r in reps])]
            f.sort(key=(lambda x: len(x)))
        else:
            f = [[[int(i) for i in reps[r]], chars[r]] for r in range(len(reps))]
        return f
    elif typ[0] == 'I' and rk == [0, 1]:
        m = int(typ[1:])
        if m % 2 == 1:
            if poids[0] > 0:
                w0 = [0]
                for i in range((m - 1) // 2):
                    w0.extend([1, 0])
                return [[], [0], [1], w0]
            else:
                raise NotImplementedError('Sorry, not yet implemented')
        else:
            w1 = []
            for i in range((m - 2) // 2):
                w1.extend([0, 1])
            if poids[0] == poids[1] and poids[0] > 0:
                return [[], [0], [1], w1 + [0, 1]]
            elif poids[0] > poids[1] and poids[1] > 0:
                return [[], [0], [1], [1, 0, 1], w1 + [0], w1 + [0, 1]]
            elif poids[0] < poids[1] and poids[0] > 0:
                return [[], [0], [1], [0, 1, 0], [1] + w1, w1 + [0, 1]]
            else:
                raise NotImplementedError('Sorry, not yet implemented')
    else:
        return False

# F distinva


def distinva(W, weightL=1, verbose=False):
    """returns a  pair of lists where the first one contains the
    distinguished involutions (as coxelms) and the second one
    contains  the corresponding  a-invariants.  This uses the
    function 'libdistinv' for the types E6, E7, E8.

    >>> W = coxeter("G", 2)
    >>> distinva(W)
    [[(0, 1), (4, 7), (6, 2), (6, 7)], [0, 1, 1, 6]]

    Thus, the 4 involutions have a-invariants  0, 1, 1, 6.

    Using the optional  argument  'weightL',  one can specify
    unequal parameters (as in 'ainvariants', for example).

    See also 'libdistinv' and 'distinguishedinvolutions'.
    """
    ti = chartable(W, chars=False)
    ch = ti['charnames']
    if isinstance(weightL, int):
        poids = len(W.rank) * [weightL]
    else:
        poids = weightL
    if len(set(poids)) == 1:
        ainv = ti['a']
        if W.cartan in [cartanmat("E", 6), cartanmat("E", 7), cartanmat("E", 8)]:
            d = libdistinv(W, 1, unpack=0)
            typEH = True
        else:
            # d=[list(l) for l in zip(*distinguishedinvolutions(W, 1))]
            d = [list(l) for l in zip(*distinguishedinvolutions_eq(W))]
            typEH = False
    else:
        d = [list(l) for l in zip(*distinguishedinvolutions(W, poids))]
        ainv = ainvariants(W, poids)
        typEH = False
    a1 = []
    if verbose:
        lprint('#I ' + str(len(d)) + ' ')
    for i in d:
        a0 = [ainv[ch.index(c[0])] for c in i[1]]
        if len(set(a0)) > 1:
            print('Mist !!!!!')
            return False
        a1.append(a0[0])
    nd, na = [], []
    for r in range(len(d)):
        if typEH:
            for st in starorbitinv(W, W.wordtoperm(d[r][0])):
                nd.append(st[:len(W.rank)])
                na.append(a1[r])
        else:
            nd.append(W.wordtocoxelm(d[r][0]))
            na.append(a1[r])
    if verbose:
        lprint('\n')
    return [nd, na]

# F distinva1


def distinva1(W, weightL):
    """similar to 'distinva' but use families not just a-invariants.
    """
    ti = chartable(W, chars=False)
    ch = ti['charnames']
    d = [list(l) for l in zip(*distinguishedinvolutions(W, weightL))]
    ainv = lusztigfamilies(W, weightL)
    aa = ainvariants(W, weightL)
    a1, a2 = [], []
    lprint('#I ' + str(len(d)) + ' ')
    for i in d:
        a0 = [ch.index(c[0]) for c in i[1]]
        aa0 = [aa[ch.index(c[0])] for c in i[1]]
        f = 0
        while (f < len(ainv['families']) and
               not all(x in ainv['families'][f] for x in a0)):
            f += 1
        if f >= len(ainv['families']):
            print('Mist !!!!!')
            return False
        a1.append(f)
        a2.append(aa0[0])
    nd, na, nb = [], [], []
    for r in range(len(d)):
        nd.append(W.wordtocoxelm(d[r][0]))
        na.append(a1[r])
        nb.append(a2[r])
    lprint('\n')
    return [nd, na, nb]

# F gentaudistcheck


def gentaudistcheck(W):
    J = list(range(len(W.rank) - 1))
    W1 = reflectionsubgroup(W, J)
    dc = [W.coxelmtoperm(d) for d in redleftcosetreps(W, J)]
    d = distinva(W)
    dist = set(d[0])
    gt1 = gentaureps(W1)
    nset = []
    for g in gt1:
        l = []
        for x in g:
            wx = W.wordtoperm(x)
            for y in dc:
                dx = permmult(y, wx)
                if dx[:len(W.rank)] in dist:
                    l.append(dx)
        nset.extend(gentaucells(W, l))
    for n1 in nset:
        if len(n1) > 1:
            n0 = [d[1][d[0].index(w[:len(W.rank)])] for w in n1]
            print([len(n1), n0])
            if len(set(n0)) < len(n1):
                print('Mist !!!!')
                return False
    lprint('\nTrue\n')
    return True

# F klupsilonI


def klupsilonI(W):
    """returns  representatives  of the left star orbits in the
    various  tau-cells of the set  UpsilonI(W).  If an orbit
    contains a distinguished involution then this involution
    is taken as representatives; otherwise, it is checked if
    if there is at least some involution;  if yes, then this
    is  taken as  representative,  otherwise,  an element of
    minimal length in the orbit is returned.
    """
    J = list(range(len(W.rank) - 1))
    W1 = reflectionsubgroup(W, J)
    dc = [W.coxelmtoperm(d) for d in redleftcosetreps(W, J)]
    gt1 = [c.X for c in klcells(W1, 1, lpol([1], 1, 'v'))[1]]
    dd = set(distinva(W)[0])
    nset = []
    for g in gt1:
        l = []
        for x in g:
            wx = W.wordtoperm(x)
            for y in dc:
                dx = permmult(y, wx)
                l.append(dx)
        # nset.extend(gentaucells(W, l, lcells=True))
        n1set = [leftklstarreps(W, l1, dd) for l1 in gentaucells(W, l, lcells=True)]
        nset.extend([[w[:len(W.rank)] for w in nn] for nn in n1set])
    lprint(str(len(nset)) + '\n')
    return nset

# F klupsilonI1


def klupsilonI1(W):
    """similar to 'klupsilonI' but returns only those left star
    orbits which need further consideration.
    """
    J = list(range(len(W.rank) - 1))
    W1 = reflectionsubgroup(W, J)
    dc = [W.coxelmtoperm(d) for d in redleftcosetreps(W, J)]
    gt1 = [c.X for c in klcells(W1, 1, lpol([1], 1, 'v'))[1]]
    dd = set(distinva(W)[0])
    nset = []
    n1 = 0
    for g in gt1:
        l = []
        for x in g:
            wx = W.wordtoperm(x)
            for y in dc:
                dx = permmult(y, wx)
                l.append(dx)
        for gt in gentaucells(W, l, lcells=True):
            if len([x for x in gt if x[:len(W.rank)] in dd]) == 1:
                lprint('!')
                n1 += 1
            else:
                for lgt in leftklstarreps(W, gt, dd):
                    if W.permorder(lgt) <= 2:
                        lprint('?')
                    else:
                        lprint('-')
                        nset.append(lgt[:len(W.rank)])
    lprint(str(n1) + ' Zellen und ' + str(len(nset)) + ' Verbrecher\n')
    return nset


def checkatau(W):
    a = distinva(W)
    af = False
    for l in gentaucells(W, a[0], string=True):
        a1 = [a[1][a[0].index(x[:len(W.rank)])] for x in l]
        if len(set(a1)) < len(a1):
            if af is False:
                af = distinva1(W, 1)
            print('#I Using families, not just a-invariants!')
            af1 = [af[1][af[0].index(x[:len(W.rank)])] for x in l]
            if len(set(af1)) < len(af1):
                print([a1, af1, l])
                return False
    return True

# F cellsinvolutions


def cellsinvolutions(W):
    """returns the partition of involutions into two-sided cells.

    """
    t = chartable(W, chars=0)
    sp = [t['charnames'][i] for i in range(len(t['a'])) if t['a'][i] == t['b'][i]]
    # gt=gentaucells(W, ii)
    d = distinguishedinvolutions(W, 1, distonly=0)
    ind = [i for i in range(len(d[0])) if W.permorder(W.wordtoperm(d[0][i])) <= 2]
    twos = []
    for s in sp:
        t1 = []
        for i in ind:
            if s in set([j[0] for j in d[1][i]]):
                t1.append(d[0][i])
        twos.append(t1)
    return [twos, sp]


def leftcellsinvolutions(W):
    """returns the partition of involutions into left cells
    (conjecturally).
    """
    t = chartable(W, chars=0)
    isp = [i for i in range(len(t['a'])) if t['a'][i] == t['b'][i]]
    nsp = sum([chartable(W)['irreducibles'][i][0] for i in isp])
    sp = [t['charnames'][i] for i in isp]
    ii = involutions(W)
    d = distinguishedinvolutions(W, 1, distonly=0)
    ind = [i for i in range(len(d[0])) if W.permorder(W.wordtoperm(d[0][i])) <= 2]
    twos = []
    for s in sp:
        t1 = []
        for i in ind:
            if s in set([j[0] for j in d[1][i]]):
                t1.append(d[0][i])
        twos.append(t1)
    c = [set([W.wordtocoxelm(p) for p in l]) for l in twos]
    g = [set([p[:len(W.rank)] for p in l]) for l in gentaucells(W, ii)]
    neu = []
    for l1 in g:
        for l2 in c:
            l3 = [x for x in l1 if x in l2]
            if l3:
                neu.append([W.coxelmtoword(x) for x in l3])
    lprint('# Number of left cells = ' + str(nsp) + '/' + str(len(neu)) + '\n')
    return neu

# F twosidedcells


def twosidedcells(W, lcells):
    """returns the partition of W into two-sided cells from the given
    partition into left cells.  (It is assumed here that Lusztig's
    property (A) holds.)
    """
    pl = [[W.wordtoperm(w) for w in l] for l in lcells]
    pr = [set([perminverse(w)[:len(W.rank)] for w in l]) for l in pl]
    mat = [[len([x for x in pl[i] if x[:len(W.rank)] in pr[j]])
            for j in range(len(pr))] for i in range(len(pl))]
    two = []
    for b in decomposemat(mat):
        l = []
        for i in b:
            l.extend(lcells[i])
        two.append(l)
    return two

# F Data to construct the left cells in type E7 and E8


E7KLCELLREPS = [{"a": 0, "distinv": "", "replstar": [""], "special": "1_a",
  "elms": [], "character": [["1_a", 1]], "size": 1}, {"a": 63, "distinv":
  "012031203243120324315431203243154320654312032431543206543123456",
  "replstar": ["0120312032431203243154312032431543206543120324315432065" +
  "43123456"], "special": "1_a'", "elms": [], "character": [["1_a'", 1]],
  "size": 1}, {"a": 1, "distinv": "0", "replstar": ["0"], "special": "7_a'",
  "elms": [], "character": [["7_a'", 1]], "size": 7}, {"a": 46, "distinv":
  "12031203243120324315431203243154320654312032431543206543123456",
  "replstar": ["012031203243120324315431203243154320654312032431543265431"],
  "special": "7_a", "elms": [], "character": [["7_a", 1]], "size": 7},
  {"a": 3, "distinv": "654312032431543206543123456", "replstar":
  ["143206543123456"], "special": "21_b'", "elms": [], "character":
  [["21_b'", 1]], "size": 21}, {"a": 36, "distinv":
  "012031203243120324315431203243154320", "replstar":
  ["012031203243120324315431203243154320"], "special": "21_b", "elms": [],
  "character": [["21_b", 1]], "size": 21}, {"a": 2, "distinv": "02314320",
  "replstar": ["14320"], "special": "27_a", "elms": [], "character":
  [["27_a", 1]], "size": 27}, {"a": 37, "distinv":
  "1231234312345431203243154320654312032431543206543123456", "replstar":
  ["0120312032431203243154312032431543206543123456"], "special": "27_a'",
  "elms": [], "character": [["27_a'", 1]], "size": 27}, {"a": 3, "distinv":
  "02345654320", "replstar": ["0203456", "123432056"], "special": "56_a'",
  "elms": [], "character": [["56_a'", 1], ["21_a", 1]], "size": 77},
  {"a": 30, "distinv": "123123431203243154312032431543206543120324315432",
  "replstar": ["12312343123454312345654312032431543265431",
  "012031203243120324315431203243546543120324315432"], "special": "56_a",
  "elms": [], "character": [["56_a", 1], ["21_a'", 1]], "size": 77}, {"a": 3,
  "distinv": "02314325431654320", "replstar": ["2431654320",
  "020314325431654320", "12343120325431654320"], "special": "56_a'",
  "elms": [], "character": [["56_a'", 1], ["35_b", 1]], "size": 91},
  {"a": 30, "distinv": "123123431234543123456543123456", "replstar":
  ["123123431234543123456543123456",
  "12312034312032435431203243154326543123456",
  "1231234312034543120324354654312032431543265431"], "special": "56_a",
  "elms": [], "character": [["56_a", 1], ["35_b'", 1]], "size": 91},
  {"a": 15, "distinv": "023143205431203243154320654312032431543206543123456",
  "replstar": ["131431543120326543120324315432065"], "special": "105_c'",
  "elms": [], "character": [["105_c'", 1]], "size": 105}, {"a": 12,
  "distinv": "123123431234", "replstar": ["123123431234"], "special": "105_c",
  "elms": [], "character": [["105_c", 1]], "size": 105}, {"a": 6, "distinv":
  "03123431203254316543120324315436", "replstar": ["0120343123565431203",
  "123431203254316543120324315436"], "special": "105_b", "elms": [],
  "character": [["105_b", 1]], "size": 105}, {"a": 21, "distinv":
  "1203143154312032435465431203245", "replstar":
  ["02032043205432065431203245", "0131431543126543120324315432654"],
  "special": "105_b'", "elms": [], "character": [["105_b'", 1]], "size": 105},
  {"a": 6, "distinv": "023454312032431654312032435465", "replstar":
  ["012034312354654320", "12343120325431654312032435465"], "special": "105_b",
  "elms": [], "character": [["105_b", 1]], "size": 105}, {"a": 21, "distinv":
  "123120343120324354320654312032431", "replstar":
  ["020320432054320654312032431", "01314315431654312032431543265431"],
  "special": "105_b'", "elms": [], "character": [["105_b'", 1]], "size": 105},
  {"a": 4, "distinv": "031436", "replstar": ["01436", "02031436",
  "1234312036"], "special": "120_a", "elms": [], "character": [["120_a", 1],
  ["15_a'", 1]], "size": 135}, {"a": 25, "distinv":
  "120314312543120324315432065431203243154320654312345", "replstar":
  ["0120312032431203243154312032435465431203245",
  "0203204312054312032465431203243154320654312345",
  "0203204312032543120324315465431203243154320654312345"], "special":
  "120_a'", "elms": [], "character": [["120_a'", 1], ["15_a", 1]], "size":
  135}, {"a": 6, "distinv": "02314320654312032431543206", "replstar":
  ["0204315431203456"], "special": "168_a", "elms": [], "character":
  [["168_a", 1]], "size": 168}, {"a": 21, "distinv":
  "1231234312345431203243154320654312345", "replstar":
  ["01203120324312032431654312345"], "special": "168_a'", "elms": [],
  "character": [["168_a'", 1]], "size": 168}, {"a": 7, "distinv":
  "0231432054312345654312032431543206543123456", "replstar":
  ["1314312032543165431203456"], "special": "189_c'", "elms": [],
  "character": [["189_c'", 1]], "size": 189}, {"a": 20, "distinv":
  "12312343123454312345", "replstar": ["12312343123454312345"], "special":
  "189_c", "elms": [], "character": [["189_c", 1]], "size": 189}, {"a": 5,
  "distinv": "023143205654312032431543206", "replstar": ["0204312345654320",
  "1234312032543165431203456"], "special": "189_b'", "elms": [], "character":
  [["189_b'", 1]], "size": 189}, {"a": 22, "distinv":
  "123123431234543120324315432654312345", "replstar":
  ["0203204320543206543120324315432", "123123431234543120324315432654312345"],
  "special": "189_b", "elms": [], "character": [["189_b", 1]], "size": 189},
  {"a": 5, "distinv": "0312343123565431203", "replstar": ["124354312036",
  "12343123565431203"], "special": "189_b'", "elms": [], "character":
  [["189_b'", 1]], "size": 189}, {"a": 22, "distinv":
  "12031431205431203243154326543120324315432654", "replstar":
  ["123123431203454312032435465431203245",
  "020320432054312032456543120324315432654"], "special": "189_b", "elms": [],
  "character": [["189_b", 1]], "size": 189}, {"a": 6, "distinv":
  "0231432054312345654312032431543206", "replstar": ["12312034325431654320"],
  "special": "210_a", "elms": [], "character": [["210_a", 1]], "size": 210},
  {"a": 21, "distinv": "12312343123454312345654312345", "replstar":
  ["1312431235431234654312345"], "special": "210_a'", "elms": [], "character":
  [["210_a'", 1]], "size": 210}, {"a": 13, "distinv":
  "0231203431205431203243165431203", "replstar": ["0120312032543165431203",
  "0120343543120365431203243154320"], "special": "210_b'", "elms": [],
  "character": [["210_b'", 1]], "size": 210}, {"a": 10, "distinv":
  "12343123543206543120324315432654", "replstar": ["012043543126543123456",
  "2312431203243543126543123456"], "special": "210_b", "elms": [],
  "character": [["210_b", 1]], "size": 210}, {"a": 10, "distinv":
  "031204546543", "replstar": ["01204546543", "131243120324546543"],
  "special": "210_b", "elms": [], "character": [["210_b", 1]], "size": 210},
  {"a": 13, "distinv": "120324312032435431203243154365431203243154320654312",
  "replstar": ["01203120324354312365431203243154",
  "01203432543120324365431203243154320654312"], "special": "210_b'",
  "elms": [], "character": [["210_b'", 1]], "size": 210}, {"a": 4, "distinv":
  "065431203456", "replstar": ["01203456", "124312065431203456"], "special":
  "120_a", "elms": [], "character": [["120_a", 1], ["105_a'", 1]],
  "size": 225}, {"a": 25, "distinv": "1231203431203243543120324315432",
  "replstar": ["1231203431203243543120324315432",
  "02032043120354312032436543120324315432"], "special": "120_a'", "elms": [],
  "character": [["120_a'", 1], ["105_a", 1]], "size": 225}, {"a": 14,
  "distinv": "0231203431205431203243565431203243154320", "replstar":
  ["1231234312032431543165431203", "12312343120324354312654312032435"],
  "special": "378_a", "elms": [], "character": [["378_a", 1]], "size": 378},
  {"a": 9, "distinv": "12343123543126543123456", "replstar":
  ["1231234543654312", "1243543126543123456"], "special": "378_a'", "elms":
  [], "character": [["378_a'", 1]], "size": 378}, {"a": 14, "distinv":
  "0312034312543120324654312032431543206543", "replstar":
  ["0120312032431203454365431203", "12312343120324543165431203243154365"],
  "special": "378_a", "elms": [], "character": [["378_a", 1]], "size": 378},
  {"a": 9, "distinv": "12034312035431203654312", "replstar":
  ["0203120543654312", "23124312032543654312"], "special": "378_a'",
  "elms": [], "character": [["378_a'", 1]], "size": 378}, {"a": 13,
  "distinv": "031204543123456543120324356", "replstar":
  ["12312343120324546543", "12312343120345431206543",
  "123123431203454365431203"], "special": "420_a'", "elms": [], "character":
  [["420_a'", 1], ["84_a'", 1]], "size": 504}, {"a": 10, "distinv":
  "120324312032435431234565431203243154", "replstar":
  ["23243125431203243654312", "123123454365431203243154",
  "1231234354312365431203243154"], "special": "420_a", "elms": [],
  "character": [["420_a", 1], ["84_a", 1]], "size": 504}, {"a": 8, "distinv":
  "0234543120324315432654312032435465", "replstar": ["2312431203456543120345",
  "01312431203456543120345"], "special": "405_a", "elms": [], "character":
  [["405_a", 1], ["189_a", 1]], "size": 594}, {"a": 15, "distinv":
  "12312034312032435654312032431", "replstar": ["0203204320543120324316",
  "123123431203243154312346"], "special": "405_a'", "elms": [], "character":
  [["405_a'", 1], ["189_a'", 1]], "size": 594}, {"a": 8, "distinv":
  "0231234312543165431203", "replstar": ["124543165431203",
  "23243120324543165431203", "01203243120324543165431203"], "special":
  "405_a", "elms": [], "character": [["405_a", 1], ["216_a'", 1]], "size":
  621}, {"a": 15, "distinv": "1231431254312345654312345", "replstar":
  ["23243254312654312345", "123120343120324354312654312345",
  "01203120324315431203243154654312345"], "special": "405_a'", "elms": [],
  "character": [["405_a'", 1], ["216_a", 1]], "size": 621}, {"a": 7,
  "distinv": "0312343120354312365431203", "replstar": ["0131254365431203",
  "245431654312032431543", "01312345431654312032431543",
  "131243120324354312365431203", "0131243120324354312365431203",
  "01203431235431203243154365431203"], "special": "315_a'", "elms": [],
  "character": [["315_a'", 1], ["280_b", 1], ["70_a'", 1]], "size": 665},
  {"a": 16, "distinv": "120314315431654312", "replstar":
  ["01314315431654312", "2324325432654312032456",
  "013143154312345654312032456", "0203204312054312032431543654312",
  "1231203431203243543120345654312", "0120312032435431206543120324315432654"],
  "special": "315_a", "elms": [], "character": [["315_a", 1], ["280_b'", 1],
  ["70_a", 1]], "size": 665}, {"a": 10, "distinv": "0543120654312032435465",
  "replstar": ["0120312032435465", "020431543120654312032435465"], "special":
  "420_a", "elms": [], "character": [["420_a", 1], ["336_a'", 1]], "size":
  756}, {"a": 13, "distinv": "1203120324312032431", "replstar":
  ["0203204312032431", "124312054312032654312032431"], "special": "420_a'",
  "elms": [], "character": [["420_a'", 1], ["336_a", 1]], "size": 756}, {"a":
  7, "distinv": "0231432543123456543120345", "replstar": ["2454316543120345",
  "013123454316543120345", "2324312032435431654320",
  "12312034325431234654320", "0120324312032435431654320",
  "012034325431203243154654320"], "special": "315_a'", "elms": [],
  "character": [["315_a'", 1], ["280_b", 1], ["280_a'", 1]], "size": 875},
  {"a": 16, "distinv": "12312343123454312365431234", "replstar":
  ["131431254312365431234", "0131431254312365431234",
  "232432543265431203243154326", "12312034312032435431203265431234",
  "01314315431234565431203243154326", "012031203243154312032431543265431234"],
  "special": "315_a", "elms": [], "character": [["315_a", 1], ["280_b'", 1],
  ["280_a", 1]], "size": 875}, {"a": 7, "distinv": "025431234565431203456",
  "replstar": ["13143120345465", "013143120345465", "123123435432065",
  "1231203454312034565", "0120343154312034565"], "special": "315_a'",
  "elms": [], "character": [["315_a'", 1], ["280_a'", 2], ["35_a'", 1]],
  "size": 910}, {"a": 16, "distinv":
  "123120324312032431543123456543120324315432", "replstar":
  ["13143154312346543120324315432", "013143154312346543120324315432",
  "1314315431654312032431543265431", "12312343120324315431203265431234",
  "02032043120325431203243165431234"], "special": "315_a", "elms": [],
 "character": [["315_a", 1], ["280_a", 2], ["35_a", 1]], "size": 910},
  {"a": 11, "distinv": "02312034315431203", "replstar": ["01314315431203",
  "0120431543165431203", "012043254312654312032435"], "special": "512_a'",
  "elms": [], "character": [["512_a'", 1], ["512_a", 1]], "size": 1024},
  {"a": 11, "distinv": "0312034354365431203", "replstar": ["034354365431203",
  "012034354365431203", "0120343543126543120324356"], "special": "512_a'",
  "elms": [], "character": [["512_a'", 1], ["512_a", 1]], "size": 1024}]


def E7CELLREPcheck():
    """checks if the elements in replstar belong to the same tau-cell,
    and if size and degrees of characters are ok.
    """
    W = coxeter("E", 7)
    t = chartable(W)
    ch = [c[0] for c in t['charnames']]
    for c in E7KLCELLREPS:
        l = [[int(s) for s in w] for w in c['replstar']]
        g = gentaucells(W, l)
        if len(g) > 1:
            return False
        # check size
        d1 = sum([i[1] * t['irreducibles'][ch.index(i[0])][0]
               for i in c['character']])
        d2 = sum([len(leftklstarorbitelm(W, W.wordtoperm(w))) for w in l])
        if not (d1 == d2 == c['size']):
            return False
    return True

# The i-th left cell in the following list contains a distinguished
# involution which is double-star equivalent to the i-th involution
# in libdistinv(W, unpack=0)


E8KLCELLREPS = [{"a": 0, "character": [["1_x", 1]], "distinv": "",
  "replstar": [""], "elms": [], "special": "1_x", "size": 1}, {"a": 1,
  "character": [["8_z", 1]], "distinv": "7", "replstar": ["7"], "elms": [],
   "special": "8_z", "size": 8}, {"a": 2, "character": [["35_x", 1]],
  "distinv": "765431234567", "replstar": ["765431234567"], "elms": [],
  "special": "35_x", "size": 35}, {"a": 3, "character": [["112_z", 1],
  ["28_x", 1]], "distinv": "0234567654320", "replstar": ["1234320567",
  "0234567654320"], "elms": [], "special": "112_z", "size": 140}, {"a": 3,
  "character": [["112_z", 1], ["84_x", 1]], "distinv":
  "76543120324315432065431234567", "replstar":
  ["76543120324315432065431234567", "565431203243154320765431234567",
  "765431203243154320654312345676543120324315432065431234567"], "elms": [],
  "special": "112_z", "size": 196}, {"a": 4, "character": [["160_z", 1],
  ["210_x", 1]], "distinv": "07654312034567", "replstar": ["07654312034567",
  "1243120654312034567"], "elms": [], "special": "210_x", "size": 370},
  {"a": 4, "character": [["210_x", 1], ["50_x", 1]], "distinv": "031436",
  "replstar": ["031436", "02031436", "031234312036"], "elms": [],
  "special": "210_x", "size": 260}, {"a": 5, "character": [["560_z", 1]],
  "distinv": "02345676543120324315432065431234567654320", "replstar":
  ["123431203254316543207654312034567",
  "02345676543120324315432065431234567654320"], "elms": [], "special":
  "560_z", "size": 560}, {"a": 6, "character": [["567_x", 1]], "distinv":
  "0765431203243154320654312345676543120324315432065431234567", "replstar":
  ["0765431203243154320654312345676543120324315432065431234567"],
  "elms": [], "special": "567_x", "size": 567}, {"a": 6, "character":
  [["700_x", 1], ["300_x", 1]], "distinv": "0231432076543120324315432067",
  "replstar": ["014320654317654312034567", "0231432076543120324315432067",
  "123431203254316543120324317654312034567"], "elms": [], "special":
  "700_x", "size": 1000}, {"a": 6, "character": [["400_z", 1],
  ["700_x", 1]], "distinv": "0234654312032431765431203243546576",
  "replstar": ["0204315431203456543123457654320",
  "1234312032543165431203243546576", "0234654312032431765431203243546576",
  "12343120325431654312032431543265431765431203243546576",
  "02345654312032431543207654312032431543206543123457654320"], "elms": [],
  "special": "700_x", "size": 1100}, {"a": 7, "character": [["1400_z", 1],
  ["448_z", 1], ["1344_x", 1]], "distinv":
  "65431203243154320676543120324315432065431234576", "replstar":
  ["145432065431203243154320676543123456",
  "2312431203243543123654312032765431203243546576",
  "12312034325431203243654312032765431203243546576",
  "65431203243154320676543120324315432065431234576",
  "65431203243154320654312345765431203243154320654312345676543123456",
  "6543120324315432065431234567654312032431543206543123456765431203243154" +
  "3206543123456"], "elms": [], "special": "1400_z", "size": 3192},
  {"a": 7, "character": [["1400_z", 1], ["1008_z", 1], ["1344_x", 1]],
  "distinv": "023143205431234576543120324315432065431234567", "replstar":
  ["02043154312034576543120324315432067",
  "231243120325431265431207654312034567",
  "01203431235431203243165431207654312034567",
  "023143205431234576543120324315432065431234567",
  "023143205431234567654312032431543206543123456765431203243154320",
  "02314320765431203243154320654312345676543120324315432065431234567"],
  "elms": [], "special": "1400_z", "size": 3752}, {"a": 8, "character":
  [["1400_x", 1], ["1050_x", 1], ["175_x", 1]], "distinv":
  "0312343120325654312032435765431203", "replstar":
  ["0312343120325654312032435765431203", "03256543176543120324315436",
  "123120343120354312365765431203", "1231203432543120324365765431203",
  "03123431203546543120324315676543120324315436",
  "03123431203256543120324354765431203243154320654376"], "elms": [],
  "special": "1400_x", "size": 2625}, {"a": 8, "character": [["1575_x", 1],
  ["1400_x", 1], ["1050_x", 1]], "distinv": "03124367654312034567",
  "replstar": ["12312343120543676", "012043543120345676",
  "03124367654312034567", "0120343123543120345676",
  "031234312367654312034567", "0312431206765431203243154367"], "elms": [],
  "special": "1400_x", "size": 4025}, {"a": 9, "character": [["3240_z", 1]],
  "distinv": "12034312035431203654312", "replstar": ["23124312032543654312",
  "12034312035431203654312", "123431254312032437654312",
  "01203431254312032437654312"], "elms": [], "special": "3240_z", "size":
  3240}, {"a": 10, "character": [["1400_zz", 1], ["2240_x", 1]], "distinv":
  "031204546543", "replstar": ["031204546543", "131243120324546543",
  "13124312032465476543", "012034312543120324576543",
  "0312043543126543120324576543", "1231203431203543126543120324576543",
  "0120343123543120324315465476543120324356"], "elms": [], "special":
  "2240_x", "size": 3640}, {"a": 10, "character": [["1296_z", 1],
  ["2268_x", 1]], "distinv":
  "02345654320765431203243154320654312345676543120324315432065431234567",
  "replstar": ["12312343543206543120324315432067654312034567",
  "02345654320765431203243154320654312345676543120324315432065431234567"],
  "elms": [], "special": "2268_x", "size": 3564}, {"a": 11, "character":
  [["4096_z", 1], ["4096_x", 1]], "distinv":
  "0231432654312032431543206576543120324315432065431234576", "replstar":
  ["012043254312065431203243156765431203456",
  "1231203454312034654312032431543206765431203456",
  "0231432654312032431543206576543120324315432065431234576"], "elms": [],
  "special": "4096_z", "size": 8192}, {"a": 7, "character": [["1400_z", 1],
  ["1008_z", 2], ["56_z", 1]], "distinv": "0265431234567654312034567",
  "replstar": ["01314312034546576", "12312343543206576",
  "012034315431203456576", "013123431234543206576",
  "0265431234567654312034567"], "elms": [], "special": "1400_z", "size":
  3472}, {"a": 12, "character": [["3360_z", 1], ["4200_x", 1]], "distinv":
  "0312343120354654312034765431203243154320654376", "replstar":
  ["012043543120365431203243154365765431203",
  "123120354654312034765431203243154320654376",
  "0312343120354654312034765431203243154320654376",
  "0131243120324354654312034765431203243154320654376"], "elms": [],
  "special": "4200_x", "size": 7560}, {"a": 8, "character": [["1575_x", 2],
  ["1400_x", 1], ["350_x", 1]], "distinv":
  "0234654320765431203243154320654312345676", "replstar":
  ["01312431203456543120345676", "123123454312067654312034567",
  "020312054312034567654312034567", "0120431254312034567654312034567",
  "0234654320765431203243154320654312345676"], "elms": [], "special":
  "1400_x", "size": 4900}, {"a": 12, "character": [["525_x", 1]], "distinv":
  "654312032431543206543123456765431203243154320654312345676543120324315" +
  "432065431234567", "replstar": ["6543120324315432065431234567654312032" +
  "43154320654312345676543120324315432065431234567"], "elms": [], "special":
  "525_x", "size": 525}, {"a": 12, "character": [["4200_x", 1],
  ["840_x", 1]], "distinv":
  "023143546543120324315432067654312032431543206543123457654320",
  "replstar": ["023143546543120324315432067654312032431543206543123457654320",
  "12435436543120327654312032431543206576",
  "0231435465431203243154657654312032431543206543123456765431203456",
  "0131234312032435436543120327654312032431543206576"], "elms": [],
  "special": "4200_x", "size": 5040}, {"a": 13, "character": [["2800_z", 1],
  ["700_xx", 1]], "distinv":
  "031436765431203243154320654312345676543120324315432065431234567",
  "replstar": ["123123431203245431203654312037654312034567",
  "031436765431203243154320654312345676543120324315432065431234567",
  "031234312036765431203243154320654312345676543120324315432065431234567"],
  "elms": [], "special": "2800_z", "size": 3500}, {"a": 13, "character":
  [["4536_z", 1]], "distinv":
  "0231432056543120345676543120324315432065431234567654312032431543206",
  "replstar": ["123120345432654312076543120324315432065431234567654320",
  "012034325431203265431203243154320657654312032431543206576",
  "0231432056543120345676543120324315432065431234567654312032431543206"],
  "elms": [], "special": "4536_z", "size": 4536}, {"a": 10, "character":
  [["840_z", 1], ["2240_x", 1]], "distinv":
  "023143256543120324315432657654312032431543206576", "replstar":
  ["013143120324565431765431203456",
  "1245431206543120324315432065431765431203456",
  "023143256543120324315432657654312032431543206576",
  "0120343125431203243154654327654312032431543206576"], "elms": [],
  "special": "2240_x", "size": 3080}, {"a": 14, "character": [["2835_x", 1]],
  "distinv": "02312034312035431203243154654312032435765431203243154320",
  "replstar": ["013123431203245431654317654312032431543206543127654320",
  "02312034312035431203243154654312032435765431203243154320"], "elms": [],
  "special": "2835_x", "size": 2835}, {"a": 9, "character": [["3240_z", 1]],
  "distinv": "023456543120324315432076543120324315432065431234567654320",
  "replstar": ["131431203265431765431203243546576",
  "12343123543120324316543120765431203243546576",
  "0120343123543120324316543120765431203243546576",
  "023456543120324315432076543120324315432065431234567654320"], "elms": [],
  "special": "3240_z", "size": 3240}, {"a": 15, "character": [["5600_z", 1],
  ["3200_x", 1]], "distinv":
  "023143205431203243154320654312032431543206543123456", "replstar":
  ["023143205431203243154320654312032431543206543123456",
  "123123431203243543123465431203276543120324315432065",
  "0231432054312032431543206543120324315432065431234567654312032431543206" +
  "543123456"], "elms": [], "special": "5600_z", "size": 8800}, {"a": 15,
  "character": [["4200_z", 1]], "distinv":
  "1203431205431234654376543120324315467", "replstar":
  ["231243123543120324565437654312", "1203431205431234654376543120324315467",
  "12312343120324354316543120324315432065437654312"], "elms": [], "special":
  "4200_z", "size": 4200}, {"a": 5, "character": [["560_z", 1]], "distinv":
  "0312343123565431203", "replstar": ["124354312036", "0312343123565431203"],
  "elms": [], "special": "560_z", "size": 560}, {"a": 16, "character":
  [["7168_w", 1], ["2016_w", 1], ["1344_w", 1], ["4480_y", 1], ["4200_y", 1],
  ["3150_y", 1], ["420_y", 1]], "distinv":
  "0231203431205431203265431765431203", "replstar":
  ["1231234312032431565431765431203", "034354365431203765431203243154320",
  "0231203431205431203265431765431203",
  "12312343120324546543765431203243154320",
  "020320431203254312032431565431765431203",
  "123120343120324315431203265431765431203",
  "131431254312346543120324315436765431203",
  "0131431254312346543120324315436765431203",
  "12312034312032431546543765431203243154320",
  "123123431203454365431203765431203243154320",
  "02312034312054312032456543765431203243154320",
  "232432543120346543120324315432065431765431203",
  "0203120431203243154365431203765431203243154320",
  "02032043120354312032431546543765431203243154320",
  "013143123543120346543120324315432065431765431203",
  "123120343120324315431203245654312032431765431203",
  "123123431203245465431234576543120324315432065437",
  "1231203431203243154312032456543765431203243154320",
  "02312034312054312032435465431203765431203243154320",
  "123120343120324315465431234576543120324315432065437",
  "023120343120543120324565431234576543120324315432065437",
  "123123431203245431654317654312032431543206543127654320",
  "1314312543120324654312032431543206543765431203243154320",
  "01314312543120324654312032431543206543765431203243154320",
  "0231203431203543120324315465431234576543120324315432065437",
  "1231203431203243154312032456543120324356765431203243154320",
  "1231234312032454326543120347654312032431543206543127654320",
  "12312034312032431543120324565431234576543120324315432065437",
  "1231203431203243154326543120347654312032431543206543127654320",
  "0231203431203543120324356543120347654312032431543206543127654320",
  "023120343120354312032431546543120324315765431203243154320654312347654" +
  "31203"], "elms": [], "special": "4480_y", "size": 22778}, {"a": 16,
  "character": [["7168_w", 2], ["5600_w", 1], ["2016_w", 1], ["5670_y", 1],
  ["4536_y", 1], ["4480_y", 1], ["4200_y", 1], ["3150_y", 1], ["2688_y", 1]],
  "distinv": "0231234312035431654312076543120324315432654317654320",
  "replstar": ["1231203431203243543120324565431765431203",
  "1314315431203465431203243154365765431203",
  "012031203243543265432076543120324315432067",
  "123120343120324354654376543120324315432067",
  "1231234312034543265432076543120324315432067",
  "1314312543120324654312032431543265431765431203",
  "01203120324312034543265432076543120324315432067",
  "01314312543120324654312032431543265431765431203",
  "012031203254654312076543120324315432654317654320",
  "1231234312034546543120345765431203243154320654376",
  "01203120324312034543120324565431203243156765431203",
  "01203120324354316543120345765431203243154320654376",
  "13143154312032431654312032431543206543123765431203",
  "23243254312036543120324315432065431237654312034567",
  "012031203243120345431203245654376543120324315432067",
  "123120343120324354312032456543120324317654312034567",
  "0203204312054312032431543265432076543120324315432067",
  "0231234312035431654312076543120324315432654317654320",
  "1231203431203243543120324565432076543120324315432067",
  "01203120324312034546543120345765431203243154320654376",
  "12312343120324354316543120345765431203243154320654376",
  "12312343120324354654312076543120324315432654317654320",
  "123120343120324315431203243654765431203243154320654376",
  "123120343120324354316543120345765431203243154320654376",
  "123123431203243154654312076543120324315432654317654320",
  "1231234312032435431654312076543120324315432654317654320",
  "01203120324543126543120324576543120324315432654317654320",
  "02312343120543126543120324576543120324315432654317654320",
  "13143125431203265431203243154320654376543120324315432067",
  "1314315431203243165431203243154320654376543120324315432067",
  "12312034312032431543120345654312032435676543120324315432067",
  "12312343120324543126543120324576543120324315432654317654320",
  "012031203245432654312037654312032431543206543123456765431203",
  "023123431205432654312037654312032431543206543123456765431203",
  "123120343120324315431203456543120345765431203243154320654376",
  "02312343120325432654312037654312032431543206543123456765431203",
  "12312034312032431543120324654312076543120324315432654317654320",
  "12312034312032431543126543120324576543120324315432654317654320",
  "123123431203243154312032456543120324354765431203243154320654376",
  "123123431203245432654312037654312032431543206543123456765431203",
  "1231234312032431543123654312032431543654765431203243154320654376",
  "012031203243543126543120324317654312032431543206543123456765431203",
  "023123431203543126543120324317654312032431543206543123456765431203",
  "123120343120324315432654312037654312032431543206543123456765431203",
  "1231203431203243543120345654312032431576543120324315432654317654320",
  "1231234312032435431236543120324317654312032431543206543123765431203",
  "023123431203254312346543120324315437654312032431543206543123456765431203",
  "123120343120324354312032435654312037654312032431543206543123456765431203",
  "0231234312035465431203243567654312032431543206543123456765431203243154" +
  "3206", "02312343120354316543120324356765431203243154320654312345676543" +
  "12032431543206", "0231234312032543123465431203243567654312032431543206" +
  "5431234567654312032431543206", "023123431203254316543120324315432654376" +
  "543120324315432065431234567654312032431543206"], "elms": [], "special":
  "4480_y", "size": 46676}, {"a": 13, "character": [["2800_z", 1],
  ["2100_x", 1]], "distinv":
  "0231456543120324315432065431234567654312032431543206543123457654320",
  "replstar": ["123123431203243543165431203243156765431203456",
  "0231456543120324315432065431234567654312032431543206543123457654320"],
  "elms": [], "special": "2800_z", "size": 4900}, {"a": 11, "character":
  [["4096_z", 1], ["4096_x", 1]], "distinv":
  "031234320565437654312032431543206543123456765431203", "replstar":
  ["1454326543120765431203243154367",
  "031234320565437654312032431543206543123456765431203",
  "03143206543123456765431203243154320654312345676543120324315436"], "elms":
  [], "special": "4096_z", "size": 8192}, {"a": 14, "character":
  [["6075_x", 1]], "distinv": "023143205654312032431543206765431203243154" +
  "320654312345676543120324315432065431234567", "replstar":
  ["1231234312032435431236543120324354657654312032431543206576",
  "02314320565431203243154320676543120324315432065431234567654312032431543" +
  "2065431234567"], "elms": [], "special": "6075_x", "size": 6075},
  {"a": 16, "character": [["7168_w", 1], ["5600_w", 1], ["1344_w", 1],
  ["5670_y", 1], ["4480_y", 1], ["4200_y", 1], ["3150_y", 1], ["1134_y", 1]],
  "distinv": "023120343120543120324654312032431765431203", "replstar":
  ["0120312032546543765431203243154320",
  "02032043120325431203243165431765431203",
  "12312343120324315431203265431765431203",
  "13143125431234654312032431543765431203",
  "013143125431234654312032431543765431203",
  "123123431234546547654312032431543206543",
  "023120343120543120324654312032431765431203",
  "1231234312345436543127654312032431543206543",
  "01203120324546543123457654312032431543206543",
  "23243254312346543120324315432065431765431203",
  "01314312354312346543120324315432065431765431203",
  "02032043120325431203243154654312032431765431203",
  "12312034312032431543120324654312032431765431203",
  "12312343120324546543123457654312032431543206543",
  "012031203243543126543123457654312032431543206543",
  "020320431203254312032431546543765431203243154320",
  "034325432654312347654312032431543206543127654320",
  "123120343120324315431203246543765431203243154320",
  "12312034312032431543123456547654312032431543206543",
  "0231203431205431203245654312032435765431203243154320",
  "012031203245432654312347654312032431543206543127654320",
  "023120343120543120324565431234567654312032431543206543",
  "232432543120324654312032431543206543765431203243154320",
  "1231234312032435654312347654312032431543206543127654320",
  "02032043120354312032431546543123457654312032431543206543",
  "013143123543120324654312032431543206543765431203243154320",
  "020320431203543120324315465431234567654312032431543206543",
  "123120343120324315431203245654312032435765431203243154320",
  "123123431203245432654312347654312032431543206543127654320",
  "0231203431203543120324315465431234567654312032431543206543",
  "1231203431203243154312032456543123457654312032431543206543",
  "12312034312032431543120324565431234567654312032431543206543",
  "12312343120324354654312376543120324315432065431234765431203",
  "02312034312035431203243565431203243154657654312032431543206543",
  "0120312032435432654312032431576543120324315432065431234765431203",
  "1231234354312032654312032431576543120324315432065431234765431203",
  "23124312035431203243154320654312347654312032431543206543127654320",
  "0231203431203543120324365431203243154367654312032431543206543127654320",
  "023120343120354312032435465431203243154367654312032431543206543127654320",
  "0231203431235431203243154365431203243154365765431203243154320654312347" +
  "65431203"], "elms": [], "special": "4480_y", "size": 32746}, {"a": 20,
  "character": [["2100_y", 1]], "distinv": "02314320543120324315432065431" +
  "2032431543206543123456765431203243154320654312345765431203243154320",
  "replstar": ["023143205431203243154320654312032431543206543123456765431" +
  "203243154320654312345765431203243154320"], "elms": [], "special":
  "2100_y", "size": 2100}, {"a": 10, "character": [["2268_x", 1],
  ["972_x", 1]], "distinv": "120324312032435431234565431203243154",
  "replstar": ["23243125431203243654312", "12034312035431234565431203243154",
  "120324312032435431234565431203243154"], "elms": [], "special": "2268_x",
  "size": 3240}, {"a": 21, "character": [["4200_z'", 1]], "distinv":
  "1203143154312032435465431203245", "replstar":
  ["0131431543126543120324315432654", "1203143154312032435465431203245",
  "12312343120324354326543120324576543120324315432654"], "elms": [],
  "special": "4200_z'", "size": 4200}, {"a": 21, "character": [["5600_z'", 1],
  ["3200_x'", 1]], "distinv": "12312343123476543120324315432065431234567",
  "replstar": ["12312343123476543120324315432065431234567",
 "231243123543123465431203243154320765431234567",
  "123123431234765431203243154320654312345676543120324315432065431234567"],
  "elms": [], "special": "5600_z'", "size": 8800}, {"a": 22, "character":
  [["2835_x'", 1]], "distinv":
  "120314312543120324315436543120324354765431203245", "replstar":
  ["013143125431236543120324315432065432765431203245",
  "120314312543120324315436543120324354765431203245"], "elms": [],
  "special": "2835_x'", "size": 2835}, {"a": 15, "character": [["4200_z", 1]],
  "distinv": "02312034312354312032431543654312032431547654312032435",
  "replstar": ["1231234312032436543127654312032435",
  "02312034312354312032431543654312032431547654312032435",
  "0120343254312032431654312032431543206543127654312032435"], "elms": [],
  "special": "4200_z", "size": 4200}, {"a": 9, "character": [["3240_z", 1]],
  "distinv": "0312343123565431237654312034567", "replstar":
  ["12312345436543120376", "12312343125436543120376",
  "01203431235431234565765431203", "0312343123565431237654312034567"],
  "elms": [], "special": "3240_z", "size": 3240}, {"a": 23, "character":
  [["4536_z'", 1]], "distinv": "123123431234543120324315432067654312345",
  "replstar": ["123123431234543120324315432067654312345",
  "013143154316543120324376543120324315432",
  "23124312354312346543120324315432067654312345"], "elms": [], "special":
  "4536_z'", "size": 4536}, {"a": 16, "character": [["7168_w", 2],
  ["5600_w", 2], ["5670_y", 2], ["4536_y", 2], ["4480_y", 1], ["4200_y", 1],
  ["2688_y", 1], ["1680_y", 1], ["1400_y", 1]], "distinv":
  "023154312032436543120324315432765431203243154320654765", "replstar":
  ["013143154312365431203243154320654765",
  "12312343120324565431207654312032435465",
  "02032043120354312032431567654312032435465",
  "12312034312032431565431207654312032435465",
  "013143123543120324365431203243154320654765",
  "123123431203243154312032456543120324354765",
  "1231234312032431543120324567654312032435465",
  "12312343120346543123765431203243154320654765",
  "012031203254316543123765431203243154320654765",
  "032432543123654312345765431203243154320654765",
  "123123431203243165431237654312032431543654765",
  "1231234312032436543120327654312032431543654765",
  "02032043120354312032431565431207654312032435465",
  "020312043120324316543123765431203243154320654765",
  "0120312032543265431203243765431203243154320654765",
  "1231234312032431543120324565431207654312032435465",
  "01314312543120346543120324315432067654312032435465",
  "12312343120345465432765431203243154320654312345765",
  "020320431203543120324315432765431203243154320654765",
  "123120343120324354312032435765431203243154320654765",
  "123123431203243154316543123765431203243154320654765",
  "0254312032436543120324315432765431203243154320654765",
  "1231203431203243543123456543120324317654312032435465",
  "1231234312032431543120326543120324567654312032435465",
  "02032043120325431203243165431237654312032431543654765",
  "12312343120324315431203265431237654312032431543654765",
  "020312043120324315465432765431203243154320654312345765",
  "023154312032436543120324315432765431203243154320654765",
  "123123431203243543123654312345765431203243154320654765",
  "123123431203243543265431203243765431203243154320654765",
  "123123431234543654312032765431203243154320654312345765",
  "0120312032454365431203245765431203243154320654312345765",
  "1231203431203243543120346543123765431203243154320654765",
  "1231234312032431543120346543123765431203243154320654765",
  "1231234312032431543265431203243765431203243154320654765",
  "01314312543120345654312032431543206543127654312032435465",
  "0120312032431234543654312032765431203243154320654312345765",
  "1231234312032454365431203245765431203243154320654312345765",
  "01203120324354312365431203245765431203243154320654312345765",
  "01312343120324543120324315436543123765431203243154320654765",
  "02032043120543120324315465432765431203243154320654312345765",
  "123120343120324354312032436543120324317654312032431543654765",
  "0203120431203243154312345654312032435765431203243154320654765",
  "1231203431203243154312034565432765431203243154320654312345765",
  "1231203431203243154365431203245765431203243154320654312345765",
  "1231203431203243543120324365431203243765431203243154320654765",
  "1312431235431203243154320654312032435765431203243154320654765",
  "01314312354312346543120324315432065431237654312032431543654765",
  "02315431203243165431203243154320765431203243154320654312345765",
  "05431203246543120324315432065432765431203243154320654312345765",
  "12312343120324354312365431203245765431203243154320654312345765",
  "020320431203254312032431543265431203243765431203243154320654765",
  "0235431203246543120324315432065432765431203243154320654312345765",
  "1231234312032456543120345676543120324315432065431234576543120345",
  "12312343120324543126543120345676543120324315432065431234576543120345",
  "123120343120324315431203243565431203245765431203243154320654312345765",
  "0234543120345654312032431543206576543120324315432065431234576543120345",
  "1231203431203243154312032435654312032456765431203243154320654312345765",
  "1231234312032435465431234576543120324315432065431234567654312032435465",
  "054312032465431203243154365476543120324315432065431234567654312032435465",
  "023154312032456543120324315432065431765431203243154320654312345765431" +
  "20345", "025431203456543120324315432065431234567654312032431543206543" +
  "1234576543120345", "02354312032436543120324315432654317654312032431543" +
  "2065431234567654312032435465", "023543120324316543120324315432065431234" +
  "576543120324315432065431234567654312032435465"], "elms": [], "special":
  "4480_y", "size": 60396}, {"a": 10, "character": [["1400_zz", 1],
  ["2240_x", 1]], "distinv":
  "02314325431654312032431543276543120324315432654317654320", "replstar":
  ["012043543265431203243154657654320",
  "131243120324354654327654312032431543206576",
  "0131243120324354654327654312032431543206576",
  "0120343123543120324354657654312032431543206576",
  "02314325431654312032431543276543120324315432654317654320",
  "01203431235431203243154365431203276543120324315432654317654320",
  "023143254316543120324315432654317654312032431543206543123456765431203456"],
  "elms": [], "special": "2240_x", "size": 3640}, {"a": 15, "character":
  [["5600_z", 1], ["2400_z", 1]], "distinv": "0231432054312345654312032431" +
  "543206765431203243154320654312345676543120324315432065431234567",
  "replstar": ["13143154312032654312032431543206576543120324315432067",
  "0231432054312345654312032431543206765431203243154320654312345676543120" +
  "324315432065431234567"], "elms": [], "special": "5600_z", "size": 8000},
  {"a": 9, "character": [["3240_z", 1]], "distinv":
  "031234312032543654312032431543654765431203243154320654376", "replstar":
  ["123120343256543176543120324315436",
  "123123431205432654312032435765431203",
  "12312343543120326543176543120324315436",
  "031234312032543654312032431543654765431203243154320654376"], "elms": [],
  "special": "3240_z", "size": 3240}, {"a": 16, "character": [["7168_w", 1],
  ["5600_w", 2], ["448_w", 1], ["5670_y", 2], ["4536_y", 1], ["4480_y", 1],
  ["3150_y", 1], ["1680_y", 1], ["1134_y", 1]], "distinv":
  "02315431203243156543120324576543120324315432065431234765", "replstar":
  ["0203204312054312032431546576543120345",
  "12312034312032431565431276543120324354657",
  "012031203254365431203765431203243154320654765",
  "123120343120324316543765431203243154320654765",
  "131431543120324654312032431543206576543120345",
  "0131431543120324654312032431543206576543120345",
  "0203204312035431203243156543120345676543120345",
  "02032043120354312032431565431276543120324354657",
  "13143154312032654312032431543206543176543120345",
  "123123431203243154312032456543120345676543120345",
  "01314312543120346543120324315432676543120324354657",
  "12312343120324354365431203765431203243154320654765",
  "12312343120345465432076543120324315432065431234765",
  "123123431203243154365431203765431203243154320654765",
  "12312345431206543120324576543120324315432065431234765",
  "012031203243120345465432076543120324315432065431234765",
  "0120312032454316543120324576543120324315432065431234765",
  "0203204312035431203243546576543120324315432065431234765",
  "1314312543120346543120324315432065431276543120324354657",
  "01314312543120346543120324315432065431276543120324354657",
  "02315431203243156543120324576543120324315432065431234765",
  "0120312032431203456543120324576543120324315432065431234765",
  "0203204312032543120324315436543120324315676543120324354657",
  "1231203431203243154312032436543120324315676543120324354657",
  "1231234312032454316543120324576543120324315432065431234765",
  "02032043120325431203243154365431203765431203243154320654765",
  "02032043120543120324315465432076543120324315432065431234765",
  "1231203431203243154316543120324576543120324315432065431234765",
  "02032043120325431203243154654312032435765431203243154320654765",
  "02032043120543120324315432654312032435765431203243154320654765",
  "12312034312032431543120324654312032435765431203243154320654765",
  "12312034312032435431203245654312032435765431203243154320654765",
  "0235431203243156543120345765431203243154320654312345676543120345",
  "1231234312032456543120345765431203243154320654312345676543120345",
  "01203120324543126543120345765431203243154320654312345676543120345",
  "123123431203243154312034565431203245676543120324315432065431234765",
  "123123431203243543123654312032456765431203243154320654312347654320",
  "1231203431203243156543120345765431203243154320654312345676543120345",
  "01203120324354312032654312032431543206543123765431203243154320654765",
  "12312343120324543126543120345765431203243154320654312345676543120345",
  "12312034312032431543126543120345765431203243154320654312345676543120345",
  "023154312032435465431203243154320765431203243154320654312345676543120345",
  "023454312032431543206543120324315765431203243154320654312345676543120345",
  "023543120324354654312032431546765431203243154320654312345676543120324" +
  "35465", "0254312032431543265431203243154676543120324315432065431234567" +
  "654312032435465", "0231543120324315436543120324315436547654312032431543" +
  "20654312345676543120324315432065", "0234543120324315432065431203243546" +
  "57654312032431543206543123456765431203243154320654312345"], "elms": [],
  "special": "4480_y", "size": 45136}, {"a": 12, "character": [["3360_z", 1],
  ["4200_x", 1]], "distinv":
  "0312343120565437654312032431543206543123456765431203", "replstar":
  ["01454326543120765431203243154367",
  "1231203454326543120765431203243154367",
  "0312343120565437654312032431543206543123456765431203",
  "031234312032543654312037654312032431543206543123456765431203"],
  "elms": [], "special": "4200_x", "size": 7560}, {"a": 6, "character":
  [["400_z", 1], ["700_x", 1]], "distinv": "03123431203254316543120324315436",
  "replstar": ["0120343123565431203", "020314326543176543120324315436",
  "03123431203254316543120324315436", "12343120326543176543120324315436",
  "031234312032543165431203243154326543176543120324315436"], "elms": [],
  "special": "700_x", "size": 1100}, {"a": 28, "character": [["1400_zz'", 1],
  ["2240_x'", 1]], "distinv": "12031431543120324354654320765431203245",
  "replstar": ["12031431543120324354654320765431203245",
  "0120312032431203243154320654320765431203245",
  "12312343120324315431203243154320654320765431203245",
  "120314315431203243546543120345676543120324315432654765",
  "0131431543123456543120345676543120324315432654765",
  "02032043120325431203243156543120324315432065432765431203245",
  "12312343120345431203243546543120345676543120324315432654765"], "elms": [],
  "special": "2240_x'", "size": 3640}, {"a": 21, "character": [["5600_z'", 1],
  ["2400_z'", 1]], "distinv": "12312343123454312345654312345", "replstar":
  ["12312343123454312345654312345", "123123431234543123457654312345"],
  "elms": [], "special": "5600_z'", "size": 8000}, {"a": 30, "character":
  [["2268_x'", 1], ["972_x'", 1]], "distinv": "03120454312345654312032435" +
  "6765431203243154320654312345676543120324315432065431234567", "replstar":
  ["12312034312032431543120324315432065431203243154320654765431203243567",
  "0312045431234565431203243567654312032431543206543123456765431203243154" +
  "32065431234567", "031203431254312345654312032435676543120324315432065" +
  "4312345676543120324315432065431234567"], "elms": [], "special": "2268_x'",
  "size": 3240}, {"a": 16, "character": [["7168_w", 1], ["5600_w", 1],
  ["1344_w", 1], ["5670_y", 1], ["4536_y", 1], ["4480_y", 1], ["4200_y", 2],
  ["1400_y", 1], ["168_y", 1]], "distinv":
  "031203431254312345654312345676543120324356", "replstar":
  ["131431254312346543120324576543", "0131431254312346543120324576543",
  "03120454312345654312345676543120324356",
  "031203431254312345654312345676543120324356",
  "232432543126543120324315432065476543",
  "0312043154312345654312032431546576543120324356",
  "012031203245465431234576543120324356",
  "0120312032435431265431234576543120324356",
  "01314312543123456543120324315432065476543",
  "0343254326543127654312032431543206543765",
  "02032043120324315465476543120324356",
  "020320431203243154365431276543120324356",
  "12312034312032435431203246543120324576543",
  "123120343120324354312032465476543120324356",
  "123120343120324315465431234576543120324356",
  "02032043120543120324565431234576543120324356",
  "020320431203245431203243154326543120324576543",
  "0203204312032454312032431543265476543120324356",
  "020320431203543120324315465431234576543120324356",
  "34354365431203243576543120324315432065431276543",
  "0120312032454326543127654312032431543206543765",
  "123120343120324315431234565476543120324356",
  "12312034312032431543120324565431234576543120324356",
  "1312431203254312032431543206543120324576543120324356",
  "123123431203243154312654312032431543265476543120324356",
  "020320431205431203245654312345676543120324356",
  "0203204312035431203243154654312345676543120324356",
  "013143123543120324654312032431543265476543120324356",
  "031204354312346543120324315467654312032431543206543765",
  "123120343120324356543127654312032431543206543765",
  "03120343543123456543120324315467654312032431543206543765",
  "03120431543120346543120324315467654312032431543206543765",
  "123123431203243546543276543120324315432065431276543",
  "1231203431203243154326543127654312032431543206543765",
  "1231203431203243543120324356543127654312032431543206543765",
  "0120312032435436543120324317654312032431543206543765",
  "01203120324354365431203243576543120324315432065431276543",
  "0203204312035431203243154326543127654312032431543206543765",
  "1231234354312036543120324317654312032431543206543765",
  "03120343123543123465431203243546576543120324315432065431276543",
  "031204312543123456543120324315432654376543120324315432065431276543",
  "123120343120324315431203245654312345676543120324356",
  "231243120354312032431543206543127654312032431543206543765",
  "012031203243120345436543120324317654312032431543206543765",
  "0120312032431203454365431203243576543120324315432065431276543",
  "020312043120324315431203456543120324315467654312032431543206543765",
  "031204543123456543120324315432067654312032431543206543123457654312032435",
  "131431254312032431654312032431543206543127654312032431543206543765",
  "0312034312543123456543120324315432067654312032431543206543123457654312" +
  "032435"], "elms": [], "special": "4480_y", "size": 38766}, {"a": 25,
  "character": [["2800_z'", 1], ["2100_x'", 1]], "distinv":
  "1231234312034543120324354676543120324315432", "replstar":
  ["1231234312034543120324354676543120324315432",
  "02032043205431203243546543120324315432654317"], "elms": [], "special":
  "2800_z'", "size": 4900}, {"a": 21, "character": [["4200_z'", 1]],
  "distinv": "123120343120324354320654312032431", "replstar":
  ["020320432054320654312032431", "123120343120324354320654312032431",
  "123123431203243543265431203457654312032431543265431"], "elms": [],
  "special": "4200_z'", "size": 4200}, {"a": 13, "character": [["4536_z", 1]],
  "distinv": "03123431203265431234567654312032431543206543123456765431203" +
  "24315436", "replstar": ["0203204312032456543120765431203243154367",
  "0312343120326543123456765431203243154320654312345676543120324315436",
  "123120345432654312032435765431203243154320654312345676"], "elms": [],
  "special": "4536_z", "size": 4536}, {"a": 26, "character": [["4096_z'", 1],
  ["4096_x'", 1]], "distinv":
  "1231234312034543120324315432065432076543120324315432", "replstar":
  ["0203204320543120324316543120324315432067654312345",
  "1231234312034543120324315432065432076543120324315432",
  "013143154312346543120345676543120324315432065431234765431234"],
  "elms": [], "special": "4096_x'", "size": 8192}, {"a": 24, "character":
  [["3360_z'", 1], ["4200_x'", 1]], "distinv":
  "1203143154312032435465431203245676543120324315432654", "replstar":
  ["013143154312345654312345676543120324315432654765",
  "01203120324312032431543165431276543120324315432654",
  "1203143154312032435465431203245676543120324315432654",
  "013143154312365431203243156765431203243154320654312347654312"], "elms": [],
  "special": "4200_x'", "size": 7560}, {"a": 22, "character":
  [["6075_x'", 1]], "distinv": "12031431205431203243154326543120324315432654",
  "replstar": ["123123431203454312032435465431203245",
  "12031431205431203243154326543120324315432654"], "elms": [], "special":
  "6075_x'", "size": 6075}, {"a": 24, "character": [["3360_z'", 1],
  ["4200_x'", 1]], "distinv":
  "120314315431203243154654312032431543265476543120324315432654", "replstar":
  ["13143154312346543120324576543120324315432654",
  "120314315431203243154654312032431543265476543120324315432654",
  "0120312032431203243154326543120324576543120324315432654",
  "12031431235431203243154326543120324315432065431276543120324315432654"],
  "elms": [], "special": "4200_x'", "size": 7560}, {"a": 36, "character":
  [["525_x'", 1]], "distinv": "012031203243120324315431203243154320",
  "replstar": ["012031203243120324315431203243154320"], "elms": [],
  "special": "525_x'", "size": 525}, {"a": 22, "character": [["6075_x'", 1]],
  "distinv": "12312343123454312032431543267654312345", "replstar":
  ["02032043205432065431203243154327",
  "12312343123454312032431543267654312345"], "elms": [], "special": "6075_x'",
  "size": 6075}, {"a": 14, "character": [["6075_x", 1]], "distinv":
  "0312343123565431203765431203243154320654312345676543120324315432065431" +
  "234567", "replstar": ["1231203431203243154312654312032437654312034567",
  "031234312356543120376543120324315432065431234567654312032431543206543" +
  "1234567"], "elms": [], "special": "6075_x", "size": 6075}, {"a": 10,
  "character": [["1400_zz", 1], ["2240_x", 1]], "distinv":
  "031234312032543165431203243154327654312032431543206543123765431203",
  "replstar": ["01204354312365431203243154365765431203",
  "124354312032654312032431543206543123765431203",
  "13124312032435465431234765431203243154320654376",
  "013124312032435465431234765431203243154320654376",
  "031234312032543165431203243154327654312032431543206543123765431203",
  "2312431203243543123654312032431543654765431203243154320654376",
  "031234312032543165431203243154326543176543120324315432065431234567654" +
  "3120324315436"], "elms": [], "special": "2240_x", "size": 3640}, {"a": 37,
  "character": [["1400_z'", 1], ["448_z'", 1], ["1344_x'", 1]], "distinv":
  "0120312032431203243154312032431543207", "replstar":
  ["0120312032431203243154312032431543207",
  "12312343123454312345654312032431543206543123457",
  "0120312032431203243154312032431543206765431203243154320",
  "1231234312345431203456543120324315432065431234765431203243154320",
  "1231203431203243543120324315432654312032431543206765431203243154320",
  "0120312032431203243154312032431543206543123457654312032431543206543" +
  "123457"], "elms": [], "special": "1400_z'", "size": 3192}, {"a": 31,
  "character": [["3240_z'", 1]], "distinv": "1203143120543120324315432654" +
  "3120324315432065476543120324315432065431234576543120324315432",
  "replstar": ["123123431234543120324354654312032431543206543127654312032" +
  "4315432654", "0203204320543120654312032457654312032431543206543123457" +
  "6543120324315432", "01203120324312032431543120324315465431203243154326" +
  "5476543120324315432654", "1203143120543120324315432654312032431543206" +
  "5476543120324315432065431234576543120324315432"], "elms": [], "special":
  "3240_z'", "size": 3240}, {"a": 25, "character": [["2800_z'", 1],
  ["700_xx'", 1]], "distinv":
  "120314312543120324315432065431203243154320654312345", "replstar":
  ["0120312032431203243154312032435465431203245",
  "120314312543120324315432065431203243154320654312345",
  "120312343120324543120324315432065431203243154320654312345"], "elms": [],
  "special": "2800_z'", "size": 3500}, {"a": 13, "character": [["4536_z", 1]],
  "distinv": "02314320654312032431543206543123457654312032431543206543123" +
  "4567654312032431543206", "replstar":
  ["02045431654312034576543120324315432065431234576",
  "012034354312032465431203243154320654327654312032431543206576",
  "0231432065431203243154320654312345765431203243154320654312345676543120" +
  "32431543206"], "elms": [], "special": "4536_z", "size": 4536}, {"a": 42,
  "character": [["400_z'", 1], ["700_x'", 1]], "distinv":
  "120314315431203243546543207654312032431543206543123456765431203245",
  "replstar":
  ["12312034312032435431203243154326543120345676543120324315432654765",
  "120314315431203243546543207654312032431543206543123456765431203245",
  "0120312032431203243154312032431543206543120345676543120324315432654765",
  "0203204312054312032654312032431546765431203243154320654312345676543120" +
  "324315432654", "120314315431203243546543120324576543120324315432065431" +
  "2345676543120324315432065431234567"], "elms": [], "special": "700_x'",
  "size": 1100}, {"a": 16, "character": [["7168_w", 1], ["5600_w", 2],
  ["448_w", 1], ["5670_y", 3], ["4536_y", 3], ["4480_y", 1], ["1680_y", 3],
  ["1400_y", 2], ["70_y", 1]], "distinv":
  "0231543120654312032431543207654312032431543206543123456765", "replstar":
  ["1314315431203265431203243154320654765",
  "01314315431203265431203243154320654765",
  "02032043120543120324315465431203456765",
  "020320431205431203243154657654312034567",
  "131431543120324365431203243154320654765",
  "1231234312032456543120765431203243546576",
  "12312034312032431543120345657654312034567",
  "0203204312035431203243156765431203243546576",
  "1231203431203243156543120765431203243546576",
  "12312343120324654320765431203243154320654765",
  "123123431203243154312032456765431203243546576",
  "123123543120654312032765431203243154320654765",
  "01203120325431654312032765431203243154320654765",
  "02032043120354312032435765431203243154320654765",
  "12312034312032431654320765431203243154320654765",
  "13143154312032465431203243154320657654312034567",
  "013143154312032465431203243154320657654312034567",
  "020320431203543120324315654312034567654312034567",
  "0203204312035431203243156543120765431203243546576",
  "1314315431203265431203243154320654317654312034567",
  "01203120324312034654312032765431203243154320654765",
  "23124312035431203243154320765431203243154320654765",
  "123123431203243154312032456543120765431203243546576",
  "0131431254312034654312032431543206765431203243546576",
  "1231234312032435431654312032765431203243154320654765",
  "1231234312034546543207654312032431543206543123456765",
  "12312343120324315431654312032765431203243154320654765",
  "13143154312065431203243154320654312765431203243546576",
  "23243254312065431203243154320654312765431203243546576",
  "020320431203254312032431654312032456765431203243546576",
  "1231234312032431543120324654320765431203243154320654765",
  "1231234543120654312032457654312032431543206543123456765",
  "02031204312032431546543207654312032431543206543123456765",
  "12312343120324354312365431203243765431203243154320654765",
  "12312343120324354312365431203245765431203243154320654765",
  "012031203245431654312032457654312032431543206543123456765",
  "020320431203543120324354657654312032431543206543123456765",
  "123120343120324354312034654312032765431203243154320654765",
  "123123431203243154312034654312032765431203243154320654765",
  "0131431254312034565431203243154320654312765431203243546576",
  "0231543120654312032431543207654312032431543206543123456765",
  "0254312654312034567654312032431543206543123456765431203456",
  "013123431203245431203243154365431203243156765431203243546576",
  "020312043120324315654312032457654312032431543206543123456765",
  "123123431203245431654312032457654312032431543206543123456765",
  "131243120325431203243154320657654312032431543206543123456765",
  "0131234312032454312032431543654312032765431203243154320654765",
  "0343254312654312034567654312032431543206543123456765431203456",
  "02345431654312032431567654312032431543206543123456765431203456",
  "123120343120324315431203456543207654312032431543206543123456765",
  "123120343120324315431654312032457654312032431543206543123456765",
  "0131234312032454312032431543654312032435765431203243154320654765",
  "0131234312034543120324315432654312032435765431203243154320654765",
  "054320654312032431546576543120324315432065431234567654312032435465",
  "123123431203245654312034567654312032431543206543123456765431203456",
  "1231234312032431543120345654312032457654312032431543206543123456765",
  "12312343120324354312365431203245676543120324315432065431234567654320",
  "0234543123456543120324315432067654312032431543206543123456765431203456",
  "1231234312032454312654312034567654312032431543206543123456765431203456",
  "023454312034654312032431546576543120324315432065431234567654312032435465",
  "0231543120345654312032435465765431203243154320654312345676543120324315" +
  "432065", "023454316543120345676543120324315432065431234567654312032431" +
  "5432065431234567"], "elms": [], "special": "4480_y", "size": 61824},
  {"a": 23, "character": [["4536_z'", 1]], "distinv":
  "12031431543120324315432065431203243154320765431203245", "replstar":
  ["01203120324312032431654320765431203245",
  "12031431543120324315432065431203243154320765431203245",
  "123123431234543120324315436543120324354765431203245"], "elms": [],
  "special": "4536_z'", "size": 4536}, {"a": 22, "character":
  [["2835_x'", 1]], "distinv":
  "12312034312032435431203465431203243547654312032431", "replstar":
  ["01314315431654317654312032431543265431",
  "12312034312032435431203465431203243547654312032431"], "elms": [],
  "special": "2835_x'", "size": 2835}, {"a": 30, "character":
  [["1296_z'", 1], ["2268_x'", 1]], "distinv":
  "123123431203243154312032431543206543120324315432", "replstar":
  ["12312343123454312345654312032431543265431",
  "123123431203243154312032431543206543120324315432"], "elms": [], "special":
  "2268_x'", "size": 3564}, {"a": 26, "character": [["4096_z'", 1],
  ["4096_x'", 1]], "distinv":
  "1203123431234543120324315432065431203243154320765431203245", "replstar":
  ["01203120324312032431543120324354765431203245",
  "1203123431234543120324315432065431203243154320765431203245",
  "120314312345431203243154326543120324315432065431276543120324315432654"],
  "elms": [], "special": "4096_x'", "size": 8192}, {"a": 28, "character":
  [["1400_zz'", 1], ["2240_x'", 1]], "distinv":
  "1203143120543120324315432654312032431543265476543120324315432654",
  "replstar": ["0203204320543206543120324576543120324315432654",
  "01314315431234565431203243156765431203243154320654312347654312",
  "02032043205432065431203243156765431203243154320654312347654312",
  "123123431203243154312032431543206543120324576543120324315432654",
  "1203143120543120324315432654312032431543265476543120324315432654",
  "020320431203254312032431546543120324315432065431234576543120324315432654",
  "1203143120543120324315432065431203243154326543176543120324315432065431" +
  "2347654312"], "elms": [], "special": "2240_x'", "size": 3640}, {"a": 23,
  "character": [["4536_z'", 1]], "distinv":
  "1231234312345431203243154326543276543120324315432654317", "replstar":
  ["012031203243120324315654312347654312345",
  "0131431543165431234576543120324315432654317",
  "1231234312345431203243154326543276543120324315432654317"], "elms": [],
  "special": "4536_z'", "size": 4536}, {"a": 14, "character": [["2835_x", 1]],
  "distinv": "03123431203546543120324315676543120324315432065431234567654" +
  "3120324315436", "replstar": ["0120435431654312034765431203243154320654376",
  "031234312035465431203243156765431203243154320654312345676543120324315436"],
  "elms": [], "special": "2835_x", "size": 2835}, {"a": 37, "character":
  [["1400_z'", 1], ["1008_z'", 1], ["1344_x'", 1]], "distinv":
  "1231234312345431203243154320654312032431543206543123456", "replstar":
  ["01203120324312032431543120324315432076543123456",
  "1231234312345431203243154320654312032431543206543123456",
  "123123431234543123456543120324315432065431234576543123456",
  "01203120324312032431543120324315432067654312032431543206543123456",
  "01203120324312032431543120324315654312032431543207654312032431543265431",
  "123123431234543123456543120324315432065431234567654312032431543206543" +
  "123456"], "elms": [], "special": "1400_z'", "size": 3752}, {"a": 31,
  "character": [["3240_z'", 1]], "distinv":
  "120314315431203243154654312032765431203243154320654312347654312",
  "replstar": ["123123431234543120345654312032435465765431203245",
  "1231234312345431203243156543120324315432065432765431203245",
  "12312034312032435431203243154320654312032435465765431203245",
  "120314315431203243154654312032765431203243154320654312347654312"],
  "elms": [], "special": "3240_z'", "size": 3240}, {"a": 24, "character":
  [["4200_x'", 1], ["840_x'", 1]], "distinv":
  "123123431203245431203243154365431234576543120324315432654317", "replstar":
  ["232432543123465431234576543120324315432654317",
  "12312343120324543120324315436543120324376543120324315432",
  "013143123543123465431234576543120324315432654317",
  "123123431203245431203243154365431234576543120324315432654317"], "elms": [],
  "special": "4200_x'", "size": 5040}, {"a": 15, "character": [["4200_z", 1]],
  "distinv": "03123431203254316543120324315436765431203243154320654312345" +
  "676543120324315432065431234567", "replstar":
  ["1231234312032435431654312034765431203243154320654376",
  "1231234312032454312034654312034765431203243154320654376",
  "03123431203254316543120324315436765431203243154320654312345676543120" +
  "324315432065431234567"], "elms": [], "special": "4200_z", "size": 4200},
  {"a": 28, "character": [["840_z'", 1], ["2240_x'", 1]], "distinv":
  "1231234312032435431203243154326543120347654312032431543206543123476543" +
  "1234", "replstar": ["020320432054320654312032435476543120324315432654317",
  "1231234312034543120324354654312032435476543120324315432654317",
  "0131431254312345654312032431543676543120324315432065431234765431234",
  "12312343120324354312032431543265431203476543120324315432065431234765" +
  "431234"], "elms": [], "special": "2240_x'", "size": 3080}, {"a": 28,
  "character": [["1400_zz'", 1], ["2240_x'", 1]], "distinv":
  "1203243120324543120324356543120324315436765431203243154320654312345" +
  "6765431203243154320654312", "replstar":
  ["020320432054312065431203243576543120324315432065431237654312",
  "0120312032431203243154312065431203243576543120324315432065431237654312",
  "020320432054312036543120324315436765431203243154320654312345676543120" +
  "3243154", "12312034312032431543120324315432065431203243576543120324315" +
  "432065431237654312", "12312343120345431203243154365431203243154367654312" +
  "032431543206543123456765431203243154", "1203243120324543120324356543120" +
  "3243154367654312032431543206543123456765431203243154320654312", "120324" +
  "312032435431203243154365431203243154320654312765431203243154320654312" +
  "345676543120324315432065431234567"], "elms": [], "special": "2240_x'",
  "size": 3640}, {"a": 46, "character": [["567_x'", 1]], "distinv":
  "12031203243120324315431203243154320654312032431543206543123456",
  "replstar": ["120312032431203243154312032431543206543120324315432065431" +
  "23456"], "elms": [], "special": "567_x'", "size": 567}, {"a": 63,
  "character": [["112_z'", 1], ["84_x'", 1]], "distinv":
  "012031203243120324315431203243154320654312032431543206543123456",
  "replstar": ["01203120324312032431543120324315432065431203243154320654" +
  "3123456", "12312034312032435431203243154326543120324315432065431234576" +
  "54312032431543206543123456", "01203120324312032431543120324315432065431" +
  "20324315432065431234567654312032431543206543123456"], "elms": [],
  "special": "112_z'", "size": 196}, {"a": 31, "character": [["3240_z'", 1]],
  "distinv": "1231203431203243543120324315432654312345676543120324315432" +
  "65431", "replstar": ["23124312354312346543123457654312032431543265431",
  "020320432054320654312032431765431203243154320654312345",
  "123120343120324354312032431543265431234567654312032431543265431",
  "01203120324312032431543265432765431203243154320654312347654312032431"],
  "elms": [], "special": "3240_z'", "size": 3240}, {"a": 42, "character":
  [["400_z'", 1], ["700_x'", 1]], "distinv":
  "1231203431203243543120324315432654312345676543120324315432654317",
  "replstar": ["12312343123454312345654312345676543120324315432654317",
  "1231203431203243543120324315432654312345676543120324315432654317",
  "012031203243120324315431203243154320654312345676543120324315432654317",
  "123123431234543120345654312032435465765431203243154320654312347654312" +
  "032431", "123120343120324354312032431543206543120324354657654312032431" +
  "54320654312347654312032431"], "elms": [], "special": "700_x'", "size":
  1100}, {"a": 32, "character": [["1575_x'", 1], ["1400_x'", 1],
  ["1050_x'", 1]], "distinv": "120312431203245431203243154320654312032431" +
  "5432065431234576543120324315432065431234576543120324315432", "replstar":
  ["020320432054312032654312032431546576543120324315432065431234576543120" +
  "324315432", "123120343120324354312032431543206543120324315432065476543" +
  "1203243154320654312345", "0203204320543120324654312032431543265476543" +
  "120324315432065431234576543120324315432", "120312431235431203243154320" +
  "65431203243154320654312345765431203243154320654312345765431203245",
  "12031431205431203243154320654312032431543206543123457654312032431543206" +
  "5431234576543120324315432", "12031243120324543120324315432065431203243" +
  "15432065431234576543120324315432065431234576543120324315432"], "elms": [],
  "special": "1400_x'", "size": 4025}, {"a": 21, "character":
  [["4200_z'", 1]], "distinv": "031203431235431203456543120324315432065" +
  "43127654312032431543206543123457654312032435", "replstar":
  ["0203204320543120324654312032431543265476543120324356",
  "013143125431203246543120324315432065431234576543120324356",
  "03120343123543120345654312032431543206543127654312032431543206543123" +
  "457654312032435"], "elms": [], "special": "4200_z'", "size": 4200},
  {"a": 31, "character": [["3240_z'", 1]], "distinv":
  "03120343125431203246543120324315432065437654312032431543206543123456" +
  "76543120324315432065431234567", "replstar":
  ["123123431234543120345654312032431543206547654312032431543206543765",
  "02032043205431203654312032431546765431203243154320654312345676543120" +
  "324356", "1231203431203243543120324315432065431203243154320654765431203" +
  "2431543206543765", "03120343125431203246543120324315432065437654312032" +
  "43154320654312345676543120324315432065431234567"], "elms": [], "special":
  "3240_z'", "size": 3240}, {"a": 42, "character": [["700_x'", 1],
  ["300_x'", 1]], "distinv": "123123431234543120324315432065431203243154" +
  "32065431234567654312032431543206543123457654312345", "replstar":
  ["1231234312345431234565431234567654312032431543206543123457654312345",
  "123120343120324354312032431543265431234567654312032431543206543123457" +
  "654312345", "1231234312345431203243154320654312032431543206543123456" +
  "7654312032431543206543123457654312345"], "elms": [], "special": "700_x'",
  "size": 1000}, {"a": 32, "character": [["1400_x'", 1], ["1050_x'", 1],
  ["175_x'", 1]], "distinv": "12031431543120324315432654312032431546765" +
  "431203243154320654312345676543120324315432654", "replstar":
  ["123123431234543120324565431203243154365476543120324315432654765",
  "1203143154312032431543265431203243156765431203243154320654312347654312",
  "120314312543120324315436543120324354765431203243154320654312345676543" +
  "1203245", "1231234312345431203243546543120324315432065431765431203243" +
  "15432654765", "1231203431203243154312032431543206543120324315436547654" +
  "3120324315432654765", "1203143154312032431543265431203243154676543120" +
  "3243154320654312345676543120324315432654"], "elms": [], "special":
  "1400_x'", "size": 2625}, {"a": 47, "character": [["560_z'", 1]],
  "distinv": "12031431205431203243154326543120324315432654765431203243" +
  "154320654312345676543120324315432065431234567", "replstar":
  ["012031203243120324315431203243154320654312032431543206543176543120324" +
  "315432654765", "12031431205431203243154326543120324315432654765431203" +
  "243154320654312345676543120324315432065431234567"], "elms": [],
  "special": "560_z'", "size": 560}, {"a": 32, "character": [["1575_x'", 2],
  ["1400_x'", 1], ["350_x'", 1]], "distinv": "1231203431203243543120324" +
  "3154320654312032431543265431765431203243154320654312345", "replstar":
  ["12312343123454312345654312032431543206543276543120324315432",
  "123123431234543123456543120324315432654317654312032431543265431",
  "020320432054320654312032435465765431203243154320654312347654312032431",
  "123123431234543120345654312032431543265431765431203243154320654312345",
  "123120343120324354312032431543206543120324315432654317654312032431543" +
  "20654312345"], "elms": [], "special": "1400_x'", "size": 4900}, {"a": 47,
  "character": [["560_z'", 1]], "distinv": "12312034312032435431203243" +
  "15432654312032431543206543123457654312032431543265431", "replstar":
  ["123123431234543123456543123456765431203243154320654312345765431203243" +
  "15432", "1231203431203243543120324315432654312032431543206543123457654" +
  "312032431543265431"], "elms": [], "special": "560_z'", "size": 560},
  {"a": 52, "character": [["160_z'", 1], ["210_x'", 1]], "distinv":
  "123120343120324354312032431543265431203243154320654312345676543120324" +
  "31543206543123456", "replstar": ["12312034312032435431203243154326543" +
  "120324315432065431234567654312032431543206543123456", "1231234312345431" +
  "20324356543120324315432654376543120324315432065431234576543120324315432"],
  "elms": [], "special": "210_x'", "size": 370}, {"a": 37, "character":
  [["1400_z'", 1], ["1008_z'", 2], ["56_z'", 1]], "distinv":
  "1231203243120324315431203243154320654312032431543207654312032431543" +
  "2065431234576543120324315432", "replstar":
  ["012031203243120324315431203243154320654312032435476543120324315432",
  "0120312032431203243154312032431543206543123457654312032431543265431",
  "01203120324312032431543120324315432065431234567654312032431543265431",
  "01203120324312032431543120324315432065431203243154327654312032431543" +
  "265431", "1231203243120324315431203243154320654312032431543207654312" +
  "0324315432065431234576543120324315432"], "elms": [], "special": "1400_z'",
  "size": 3472}, {"a": 52, "character": [["210_x'", 1], ["50_x'", 1]],
  "distinv": "1203123431203245431203243154320654312032431543206543123457" +
  "65431203243154320654312345676543120324315432065431234567", "replstar":
  ["012031203243120324315431203243154320654312032431543206543276543120324" +
  "31543206543123456765431203245", "1203143125431203243154320654312032431" +
  "54320654312345765431203243154320654312345676543120324315432065431234567",
  "1203123431203245431203243154320654312032431543206543123457654312032431" +
  "54320654312345676543120324315432065431234567"], "elms": [], "special":
  "210_x'", "size": 260}, {"a": 63, "character": [["112_z'", 1],
  ["28_x'", 1]], "distinv":
  "12312343120324315431203243154320654312032431543206543123456765431203" +
  "24315432065431234576543120324315432", "replstar": ["0120312032431203" +
  "243154312032431543206543120324315432065431234567654312032431543265431",
  "123123431203243154312032431543206543120324315432065431234567654312032" +
  "4315432065431234576543120324315432"], "elms": [], "special": "112_z'",
  "size": 140}, {"a": 74, "character": [["35_x'", 1]], "distinv":
  "01203120324312032431543120324315432065431203243154320654312345676543" +
  "1203243154320654312345765431203243154320", "replstar":
  ["0120312032431203243154312032431543206543120324315432065431234567654" +
  "31203243154320654312345765431203243154320"], "elms": [], "special":
  "35_x'", "size": 35}, {"a": 91, "character": [["8_z'", 1]], "distinv":
  "0120312032431203243154312032431543206543120324315432065431234567654" +
  "3120324315432065431234567654312032431543206543123456", "replstar":
  ["012031203243120324315431203243154320654312032431543206543123456765" +
  "43120324315432065431234567654312032431543206543123456"], "elms": [],
  "special": "8_z'", "size": 8}, {"a": 120, "character": [["1_x'", 1]],
  "distinv": "0120312032431203243154312032431543206543120324315432065431" +
  "23456765431203243154320654312345676543120324315432065431234567",
  "replstar": ["012031203243120324315431203243154320654312032431543206" +
  "543123456765431203243154320654312345676543120324315432065431234567"],
  "elms": [], "special": "1_x'", "size": 1}]

# sizes and star orbit lengths:

E8KLCELLREPORBITS = [[1, 1], [8, 8], [35, 35], [140, 28], [196, 84],
  [370, 160], [260, 50], [560, 510], [567, 567], [1000, 300], [1100, 350],
  [3192, 448], [3752, 896], [2625, 175], [4025, 875], [3240, 972],
  [3640, 651], [3564, 1296], [8192, 3445], [3472, 56], [7560, 2709],
  [4900, 350], [525, 525], [5040, 840], [3500, 700], [4536, 3045],
  [3080, 840], [2835, 2184], [3240, 1218], [8800, 3200], [4200, 168],
  [560, 50], [22778, 420], [46676, 1596], [4900, 2100], [8192, 651],
  [6075, 5375], [32746, 756], [2100, 2100], [3240, 972], [4200, 700],
  [8800, 3200], [2835, 651], [4200, 3332], [3240, 875], [4536, 840],
  [60396, 1092], [3640, 574], [8000, 2400], [3240, 175], [45136, 378],
  [7560, 651], [1100, 50], [3640, 175], [8000, 2400], [3240, 972],
  [38766, 168], [4900, 2100], [4200, 3332], [4536, 651], [8192, 3445],
  [7560, 2709], [6075, 700], [7560, 651], [525, 525], [6075, 5375],
  [6075, 700], [3640, 175], [3192, 448], [3240, 875], [3500, 700],
  [4536, 840], [1100, 50], [61824, 70], [4536, 651], [2835, 2184],
  [3564, 1296], [8192, 651], [3640, 574], [4536, 3045], [2835, 651],
  [3752, 896], [3240, 175], [5040, 840], [4200, 700], [3080, 840],
  [3640, 651], [567, 567], [196, 84], [3240, 1218], [1100, 350],
  [4025, 875], [4200, 168], [3240, 972], [1000, 300], [2625, 175],
  [560, 50], [4900, 350], [560, 510], [370, 160], [3472, 56], [260, 50],
  [140, 28], [35, 35], [8, 8], [1, 1]]


def E8CELLREPcheck():
    """checks if the elements in replstar belong to the same tau-cell,
    and if size and degrees of characters are ok.
    """
    W = coxeter("E", 8)
    t = chartable(W)
    ch = [c[0] for c in t['charnames']]
    for c in E8KLCELLREPS:
        l = [[int(s) for s in w] for w in c['replstar']]
        g = gentaucells(W, l)
        if len(g) > 1:
            return False
        # check size
        d1 = sum([i[1] * t['irreducibles'][ch.index(i[0])][0]
               for i in c['character']])
        d2 = sum([len(leftklstarorbitelm(W, W.wordtoperm(w))) for w in l])
        if not (d1 == d2 == c['size']):
            return False
    return True

# F klcellreps


def klcellreps(W, verbose=False):
    """returns a list of dictionaries  containing basic information about
    a set of representatives of the left cells of W (equal parameters)
    under repeated application of star operations. For W of type E7 or
    E8, this uses pre-computed data (which are in the global variables
    E7KLCELLREPS and E8KLCELLREPS). Otherwise, everything is  computed
    using general functions in this system.

    The components of the dictionary are:

    - size:      -- the number of elements in the left cell
    - elms:      -- the elements in the left cell
    - distinv:   -- the distinguished involution of the left cell
    - character: -- the irreducible characters occurring in the
      corresponding left cell representation
    - a:         -- the a-invariant of the characters
    - special:   -- the unique special representation occurring in
      the character of the left cell representation
    - index:     -- the position in this list of dictionaries

    >>> len(klcellreps(coxeter("E", 6)))    # long time
    21
    >>> len(klcellreps(coxeter("E", 7)))   # not tested
    56
    >>> len(klcellreps(coxeter("E", 8)))  # not tested
    106

    For further details, see Section 6 of:

      M. Geck and A. Halls, On the Kazhdan--Lusztig cells in
                                   type E_8, arXiv:1401.6804.

    See also 'klcellrepelm', 'cellrepstarorbit' and 'leftcellelm'.
    """
    if 'klcellreps' in dir(W):
        return W.klcellreps
    cm7 = cartanmat("E", 7)
    cm8 = cartanmat("E", 8)
    if W.cartan in [cm7, cm8]:
        if W.cartan == cm7:
            klcr = E7KLCELLREPS
        else:
            klcr = E8KLCELLREPS
        if any((len(l['elms']) == 0 or l['elms'] is False) for l in klcr):
            if verbose:
                lprint('#I =====> ' + str(len(klcr)) + ' (unpacking data) ')
            for l in range(len(klcr)):
                c = []
                for r in [W.wordtoperm([int(i) for i in w])
                          for w in klcr[l]['replstar']]:
                    c.extend([x[:len(W.rank)]
                             for x in leftklstarorbitelm(W, r)])
                if l % 10 == 0:
                    if verbose:
                        lprint('.')
                klcr[l]['elms'] = set(c)
                klcr[l]['index'] = l
            if verbose:
                lprint(' OK <=====\n')
        W.klcellreps = klcr
        return klcr
    else:
        if verbose:
            lprint('#I =====> pre-processing (done only once) <=====\n')
        klcr = [c.X for c in klcells(W, 1, v)[1]]
        dd = distinguishedinvolutions(W, 1)
        d1 = dd[0]
        d2 = [[[i[0][0], abs(i[1])] for i in l] for l in dd[1]]
        res = []
        for l in klcr:
            for i in range(len(d1)):
                if d1[i] in l:
                    res.append(i)
        neu = [[''.join(str(s) for s in d1[i]) for i in res],
               [d2[i] for i in res]]
        t = chartable(W)
        sp = [[t['charnames'][i][0], t['a'][i]] for i in range(len(t['a']))
                                                   if t['a'][i] == t['b'][i]]
        klcr1 = []
        for l in range(len(klcr)):
            lrep = leftklstarreps(W, [W.wordtoperm(x) for x in klcr[l]],
                                  [W.wordtoperm(x) for x in d1])
            c = 0
            while not sp[c][0] in [j[0] for j in neu[1][l]]:
                c += 1
            klcr1.append({'size': len(klcr[l]), 'index': l,
              'elms': set([W.wordtocoxelm(x) for x in klcr[l]]),
              'distinv': neu[0][l], 'character': neu[1][l], 'a': sp[c][1],
              'replstar': [''.join(str(s) for s in W.permtoword(x))
                           for x in lrep],
              'special': sp[c][0]})
        W.klcellreps = klcr1
        return klcr1

# F cellrepstarorbit


def cellrepstarorbit(W, c, verbose=False):
    """returns the orbit of a left cell from 'klcellreps' under the
    star operations.  Hence,  if we apply  this function  to all
    the left cells in 'klcellreps',  then we obtain all the left
    cells of W.

    >>> W = coxeter("E", 8)
    >>> c=klcellreps(W)     # not tested
    >>> a=cellrepstarorbit(W, c[1])  # not tested
    #I orbit with 8 cells

    >>> W = coxeter("E", 7); l1=[]
    >>> for c in klcellreps(W):   # not tested
    ...   for l in cellrepstarorbit(W, c):
    ...     l1.append(len(leftconnected(W, list(l['elms']), verbose=False)))
    >>> set(l1)  # not tested
    set([1])

    Thus, all left cells in type E7 are left-connected. The same
    also works for type E8 (but takes a couple of days).

    See also 'klcellreps' and 'cellrepcheck2'.
    """
    if verbose:
        lprint('#I cell of size ' + str(c['size']) + '; ')
    cc = starorbitinv(W, W.wordtoperm([int(s) for s in c['distinv']]),
                      list(c['elms']))
    if verbose:
        lprint('orbit with ' + str(len(cc[0])) + ' cells\n')
    orb = []
    for i in range(len(cc[0])):
        orb.append({'size': c['size'], 'character': c['character'], 'a': c['a'],
                    'special': c['special'], 'elms': set(cc[1][i]),
                    'index': c['index'],
                    'distinv': ''.join(str(s) for s in W.permtoword(cc[0][i]))})
        # 'replstar':[''.join(str(s) for s in W.permtoword(w))
        #                    for w in leftklstarreps(W, cc[1][i])]})
    return orb

# F klcellrepelm


def klcellrepelm(W, w, verbose=False):
    """returns a dictionary, as in 'klcellreps', corresponding to the
    given element,  but where  the components  'distiv' and 'elms'
    are left empty.  In particular, this yields the two-sided cell
    in which the element lies, and its a-invariant.

    >>> W = coxeter("E", 8)
    >>> w = conjugacyclasses(W)['reps'][10]
    >>> len(w)
    40
    >>> W.permorder(W.wordtoperm(w))
    6
    >>> klcellrepelm(W, w, verbose=False)['special']
    '4480_y'

    The function repeatedly applies star operations to w until one
    of the left cells in 'klcellreps' is reached. (If the optional
    argument 'pr' is set to 'True',  then the function prints  the
    index in the 'klcellreps' list to which w is star equivalent.)

    For further details, see Section 6 of:

      M. Geck and A. Halls, On the Kazhdan--Lusztig cells in
                                   type E_8, arXiv:1401.6804.

    When this function is run  for the first time, some data needs
    to be computed or unpacked from a  condensed  format.  So this
    will take  a few moments;  after that, the function should run
    reasonably fast.

    See also 'klcellreps', 'cellrepstarorbit' and 'leftcellelm'.
    """
    if isinstance(w, tuple) and len(w) == 2 * W.N:
        orb = [w]
    else:
        orb = [W.wordtoperm(w)]
    orb1 = set([orb[0]])
    e8c = klcellreps(W)
    while True:
        for y in orb:
            for c in range(len(e8c)):
                if y[:len(W.rank)] in e8c[c]['elms']:
                    if verbose:
                        lprint('#I cell number ' + str(c) + '\n')
                    return {'size': e8c[c]['size'], 'character': e8c[c]['character'],
                            'a': e8c[c]['a'], 'special': e8c[c]['special'],
                            'index': e8c[c]['index'], 'elms': False, 'distinv': False}
            for s in W.rank:
                for t in range(s):
                    if W.coxetermat[s][t] == 3:
                        nc = klstaroperation(W, s, t, [y])
                        if nc is not False and not nc[0][:len(W.rank)] in orb1:
                            for c in range(len(e8c)):
                                if nc[0][:len(W.rank)] in e8c[c]['elms']:
                                    if verbose:
                                        lprint('#I cell number ' + str(c) + '\n')
                                    return {'size': e8c[c]['size'], 'character':
                                            e8c[c]['character'], 'a': e8c[c]['a'],
                                            'special': e8c[c]['special'],
                                            'index': e8c[c]['index'], 'elms': False,
                                            'distinv': False}
                            orb.append(nc[0])
                            orb1.add(nc[0][:len(W.rank)])
    print('Mist !!!!')
    return False

# F cellreplstars


def cellreplstars(W, verbose=False):
    """returns a list of dictionaries (as in 'klcellreps') corresponding
    to all the left cells of W, but where only representatives of the
    elements in a given left cell under the  left star operations are
    returned  (in the component  'replstar' of  the dictionary).  The
    elements in each left star  orbit are taken as coxelms, then they
    are sorted, and the first element  in the sorted list is taken as
    representative.

    >>> W = coxeter("B", 2)
    >>> cellreplstars(W)
    [{'a': 0,
      'index': 0,
      'character': [['[[2], []]', 1]],
      'distinv': (0, 1),
      'replstar': [(0, 1)],
      'elms': False,
      'special': '[[2], []]',
      'size': 1},...
     {'a': 1,
      'index': 3,
      'character': [['[[1], [1]]', 1], ['[[1, 1], []]', 1]],
      'distinv': (4, 3),
      'replstar': [(2, 7), (6, 1), (4, 3)],
      'elms': False,
      'special': '[[1], [1]]',
      'size': 3}]

    Using this function,  one can identify the left cell in which any
    given element w lies: compute the left star orbit of w (using the
    function  'leftklstarorbitelm'),  take the elements in this orbit
    as coxelms, and  sort them. The first element  in the sorted list
    will appear in  exactly one of the 'replstar' entries of the list
    returned by 'cellreplstars'.

    The complete list of elements in the cell corresponding to such a
    dictionary is  obtained  by computing the left star orbits of the
    elements in 'replstar' (again using 'leftklstarorbitelm').

    For type E8, the function 'cellreplstars' takes  about 1 week and
    requires about 32 GB of main memory.  In this case, the output is
    also available from

       www.mathematik.uni-stuttgart.de/~geckmf/e8celldata.py

    (Just download  this file  and place  it  in the current  working
    directory. When you start PyCox, the system checks if the file is
    available;  if yes,  then  it will  automatically load and use it
    upon calling 'cellreplstars'.)

    See also 'klcellreps', 'leftcellelm' and 'leftklstarorbitelm'.
    """
    if W.cartan == cartanmat("E", 8):
        try:
            from e8celldata import E8ALLKLCELLS
        except ImportError:
            print("#I file e8celldata.py not found; using basic algorithm")
            E8ALLKLCELLS = False
        if E8ALLKLCELLS is not False:
            from e8celldata import E8ALLPOSITIVEROOTS
            if W.roots[:W.N] != E8ALLPOSITIVEROOTS:
                raise ValueError(
                    "----> WARNING: LABELLING OF ROOTS NOT OK !!! <----")
            if verbose:
                print("#I reading E8-data OK")
            e8all = []
            for x in E8ALLKLCELLS:
                e8all.append({'a': E8KLCELLREPS[x[0]]['a'], 'index': x[0],
                  'elms': False, 'character': E8KLCELLREPS[x[0]]['character'],
                  'size': E8KLCELLREPS[x[0]]['size'],
                  'special': E8KLCELLREPS[x[0]]['special'],
                  'distinv': tuple([int(i) for i in x[1].split('.')]),
                  'replstar': [tuple([int(i) for i in w.split('.')]) for w in x[2]]})
            return e8all
    neu = []
    alls = 0
    for c in klcellreps(W):
        for orb in cellrepstarorbit(W, c):
            rest = orb['elms'].copy()
            reps = []
            while rest:
                o = [x[:len(W.rank)] for x in leftklstarorbitelm(W,
                                                W.coxelmtoperm(next(iter(rest))))]
                alls += len(o)
                o.sort()
                reps.append(o[0])
                for w in o:
                    rest.remove(w)
            neu.append({'size': orb['size'], 'character': orb['character'],
                       'a': orb['a'], 'special': orb['special'],
                       'index': orb['index'], 'elms': False, 'replstar': reps,
                       'distinv': W.wordtocoxelm([int(i) for i in orb['distinv']])})
    if alls != W.order:
        print('Mist !!!')
        return False

    if verbose:
        lprint('#I Total number OK\n')
    return neu


# F leftcellelm
def leftcellelm(W, w, replstars=False, verbose=False):
    """returns the left cell with  respect to equal parameters (as
    a dictionary  with components as described in  'kcellreps')
    containing a  given element w.  This is  done in two steps:
    First, star operations are repeatedly applied to w until an
    element is found which lies in a cell in 'klcellreps'. Then
    star operations are applied  to this  cell until a  cell is
    found which contains the given w.

    This algorithm works fine if only a few elements  w need to
    be considered. Otherwise (especially in E7, E8), it is more
    efficient to first apply  the function 'cellreplstars' to W
    and then give the output as additional argument.

    >>> W = coxeter("F", 4)
    >>> t0 = time.time()
    >>> l0 = [leftcellelm(W, x) for x in allwords(W)]
    >>> time.time()-t0  # random
    9.92
    >>> r = cellreplstars(W)
    >>> t0 = time.time()
    >>> l1 = [leftcellelm(W, x, r) for x in allwords(W)]
    >>> time.time()-t0  # random
    0.22
    >>> [i['distinv'] for i in l0]==[i['distinv'] for i in l1]
    True

    See also 'klcellreps' and 'cellreplstars'.
    """
    if replstars is not False:
        orb = [x[:len(W.rank)] for x in leftklstarorbitelm(W, W.wordtoperm(w))]
        orb.sort()
        for c in replstars:
            if orb[0] in c['replstar']:
                return {'size': c['size'], 'a': c['a'], 'character': c['character'],
                  'special': c['special'], 'index': c['index'], 'elms': c['elms'],
                  'replstar': c['replstar'],
                  'distinv': ''.join(str(s) for s in W.coxelmtoword(c['distinv']))}
    if replstars is not False:
        print('Mist !!!!')
        return False
    w1 = W.wordtoperm(w)
    orb = [w1]
    orb1 = set([orb[0]])
    e8c = klcellreps(W)
    weiter = True
    c0 = -1
    while weiter:
        for y in orb:
            for c in range(len(e8c)):
                if y[:len(W.rank)] in e8c[c]['elms']:
                    weiter = False
                    c0 = c
            if weiter:
                for s in W.rank:
                    for t in range(s):
                        if W.coxetermat[s][t] == 3:
                            nc = klstaroperation(W, s, t, [y])
                            if nc is not False and not nc[0][:len(W.rank)] in orb1:
                                for c in range(len(e8c)):
                                    if nc[0][:len(W.rank)] in e8c[c]['elms']:
                                        weiter = False
                                        c0 = c
                                if weiter:
                                    orb.append(nc[0])
                                    orb1.add(nc[0][:len(W.rank)])
    if c0 == -1:
        print('Mist !!!')
        return False
    if verbose:
        lprint('#I cell of size ')
    if w1[:len(W.rank)] in e8c[c0]['elms']:
        if verbose:
            lprint(str(e8c[c0]['size']) + '\n')
        return e8c[c0]
    orb = [W.wordtoperm([int(s) for s in e8c[c0]['distinv']])]
    orb1 = set([orb[0][:len(W.rank)]])
    ncell = [[bytes(W.coxelmtoperm(x)) for x in list(e8c[c0]['elms'])]]
    if verbose:
        lprint(str(e8c[c0]['size']) + ': ')
    for d in orb:
        for s in W.rank:
            for t in range(s):
                if W.coxetermat[s][t] == 3:
                    if (d[s] >= W.N and d[t] < W.N) or (d[s] < W.N and d[t] >= W.N):
                        d1 = leftklstar(W, perminverse(leftklstar(W, d, s, t)), s, t)
                        if not d1[:len(W.rank)] in orb1:
                            if verbose:
                                lprint('.')
                            orb.append(d1)
                            orb1.add(d1[:len(W.rank)])
                            n1 = klstaroperation(W, s, t, ncell[orb.index(d)])
                            if w1 in n1:
                                if d1 not in n1:
                                    print('Mist !!!')
                                    return False
                                lprint('\n')
                                return {'size': e8c[c0]['size'], 'a': e8c[c0]['a'],
                                    'character': e8c[c0]['character'],
                                    'special': e8c[c0]['special'], 'index': e8c[c0]['index'],
                                    'elms': set([x[:len(W.rank)] for x in n1]),
                                    'distinv': ''.join(str(s) for s in W.permtoword(d1))}
                            else:
                                ncell.append([bytes(x) for x in n1])

# F klcellsclasses


def klcellsclasses(W, verbose=False):
    """determines intersections of two-sided cells with elements
    of minimal length in cuspidal classes of W.
    """
    kl1 = klcellreps(W)
    cp = [x for x in conjugacyclasses(W)['reps'] if len(set(x)) == len(W.rank)]
    if verbose:
        lprint('#I ' + str(len(cp)) + ' cuspidal casses: ')
    t = chartable(W, chars=0)
    sp = [t['charnames'][i][0] for i in range(len(t['a']))
          if t['a'][i] == t['b'][i]]
    mat = []
    for c in cp:
        c1 = cyclicshiftorbit(W, W.wordtoperm(c))
        if verbose:
            lprint(str(len(c1)) + ' ')
        cs = [klcellrepelm(W, x)['special'] for x in c1]
        row = [len([i for i in cs if i == char]) for char in sp]
        mat.append(row)
    if verbose:
        lprint('\n')
    return mat

# F cellrepcheck1


def cellrepcheck1(W, klcr):
    """checks if the elements in replstar belong to the same tau-cell,
    and if size and degrees of characters are ok.
    """
    t = chartable(W)
    ch = [c[0] for c in t['charnames']]
    for c in klcr:
        l = [[int(s) for s in w] for w in c['replstar']]
        g = gentaucells(W, l)
        if len(g) > 1:
            return False
        # check size
        d1 = sum([i[1] * t['irreducibles'][ch.index(i[0])][0]
               for i in c['character']])
        elms = []
        for w in l:
            elms.extend(leftklstarorbitelm(W, W.wordtoperm(w)))
        if not (d1 == len(elms) == c['size'] and W.wordtoperm([int(i)
                                                               for i in c['distinv']]) in elms):
            return False
    return True

# F cellrepcheck2


def cellrepcheck2(W):
    """returns True if the union over all cellrepstarorbits in
    klcellrep is the set of  all elements of W;  otherwise,
    returns False. In particular, this function creates all
    left cells of W  by computing the orbits under the star
    operations of all left cells from 'klcellreps'.

    >>> t = timer(cellrepcheck2, coxeter("E", 7))  # not tested
    #I 56 (unpacking data) ...... OK
    #I cell of size 1; orbit with 1 cells
    #I cell of size 1; orbit with 1 cells
    #I cell of size 7; orbit with 7 cells
    ...
    #I cell of size 1024; orbit with 70 cells
    192.58

    >>> t = timer(cellrepcheck2, coxeter("E", 8))  # not tested
    #I 106 (unpacking data) ...... OK
    #I cell of size 1; orbit with 1 cells
    #I cell of size 8; orbit with 8 cells
    #I cell of size 35; orbit with 35 cells
    ...
    #I cell of size 46676; orbit with 1596 cells
    #I cell of size 4900; orbit with 2100 cells
    ...
    #I cell of size 60396; orbit with 1092 cells
    #I cell of size 3640; orbit with 574 cells
    ...
    #I cell of size 61824; orbit with 70 cells
    ...
    #I cell of size 140; orbit with 28 cells
    #I cell of size 35; orbit with 35 cells
    #I cell of size 8; orbit with 8 cells
    #I cell of size 1; orbit with 1 cells
    118783.51
    True

    See also 'klcellreps' and 'cellrepstarorbit'.
    """
    alls = set()
    numb = 0
    for l in klcellreps(W):
        for x in cellrepstarorbit(W, l):
            alls.update(x['elms'])
            numb += len(x['elms'])
    return len(alls) == numb and numb == W.order

# F cellrepcheck3


def cellrepcheck3(W):
    """check for function 'cellreplstars'.
    """
    alls = set()
    for l in cellreplstars(W):
        numb = 0
        for r in l['replstar']:
            c = [x[:len(W.rank)]
                 for x in leftklstarorbitelm(W, W.coxelmtoperm(r))]
            numb += len(c)
            alls.update(c)
        if numb != l['size']:
            print('Mist !!!')
    return len(alls) == W.order

# F checkleftctd


def checkleftctd(W, verbose=False):
    """checks left-connectedness of all left cells of W.

    >>> W = coxeter("H", 3)
    >>> checkleftctd(W)
    {1}

    See also 'leftconnected'.
    """
    res = []
    cc = klcellreps(W)
    for c in range(len(cc)):
        for l in cellrepstarorbit(W, cc[c]):
            lc = len(leftconnected(W, list(l['elms']), verbose=False))
            if verbose:
                lprint(str(lc))
            res.append(lc)
        if verbose:
            lprint(' (cell no ' + str(c) + ')')
    if verbose:
        lprint('\n')
    return set(res)

# check Kottwitz conjecture


def checkkottwitz(W):
    check = []
    count = 0
    ii = involutionmodel(W)
    rr = conjugacyclasses(W)['reps']
    invcl = [w for w in rr if W.wordtocoxelm(2 * w) == tuple(W.rank)]
    elmscl = [set([x[:len(W.rank)] for x in conjugacyclass(W, W.wordtoperm(i))])
              for i in invcl]
    ti = chartable(W)
    ch = [c[0] for c in ti['charnames']]
    for cell in cellreplstars(W):
        if count % 100 == 0:
            lprint(str(count) + ' ')
        count += 1
        char = len(ch) * [0]
        for c in cell['character']:
            char[ch.index(c[0])] = c[1]
        inv = []
        for x in cell['replstar']:
            for y in leftklstarorbitelm(W, W.coxelmtoperm(x)):
                if permmult(y, y) == tuple(range(2 * W.N)):
                    inv.append(y)
        for i in range(len(invcl)):
            kott1 = len([w for w in inv if w[:len(W.rank)] in elmscl[i]])
            kott2 = sum([ii[str(invcl[i])][j] * char[j] for j in range(len(ch))])
            check.append(kott1 == kott2)
    print(len(check))
    return set(check)

##########################################################################
##
# Y Section 5: Tests
##

# F timer


def timer(func, *pargs, **kargs):
    """returns the result of applying a function and prints the time used
    in seconds. (Taken from M. Lutz's "Learning Python" book.)

    >>> t = timer(klcells, coxeter("F", 4), 1, v)  # random
    1.02
    """
    start = time.time()
    ret = func(*pargs, **kargs)
    print(time.time() - start)
    return ret

# F checksh


def checksh(W, paramL):
    """checks if the relation characterising the  Schur elements is true;

    see the help to 'schurelms'.  (This  is  a good  test for  various
    functions:  'heckechartable',  'schurelms',  'lpol', 'zeta5', ...;
    it does not yet work for type I_2(m), n>7, because some operations
    for the general cyclotomic arithmetic are not implemented.)
    """
    p = lcmschurelms(W, paramL)
    if isinstance(paramL, list):
        vs = paramL[:]
    else:
        vs = len(W.rank) * [paramL]
    gd = [divmod(p, s)[0] for s in schurelms(W, vs)]
    ti = heckechartable(W, vs)['irreducibles']
    res = [sum(gd[i] * ti[i][j] for i in range(len(gd))) for j in range(len(gd))]
    return res[0] == p and all(i == 0 for i in res[1:len(gd)])

# F test


def test():
    """runs a test suite.

    >>> test()  # long time
    """
    lprint('# ==>  Should finish in less than 1 minute CPU time\n')
    v = lpol([1], 1, 'v')
    somechecks = []
    # test all cartan types (finite and affine)
    W = coxeter('A', 1)
    chartable(W)
    W = coxeter('A', 2)
    chartable(W)
    W = coxeter('A', 3)
    chartable(W)
    somechecks.append(checksh(W, v))
    W = coxeter('A', 4)
    t = chartable(W)
    somechecks.append(ainvariants(W, 1) == t['a'])
    somechecks.append(checksh(W, v))
    W = coxeter('B', 2)
    chartable(W)
    somechecks.append(checksh(W, [v**2, v]))
    W = coxeter('B', 3)
    chartable(W)
    somechecks.append(checksh(W, [v**2, v, v]))
    somechecks.append(checksh(W, [v**2, v**3, v**3]))
    W = coxeter('B', 4)
    somechecks.append(checksh(W, v))
    t = chartable(W)
    somechecks.append(ainvariants(W, 1) == t['a'])
    lprint(str(t['a']) + '\n')
    W = coxeter('B', 5)
    chartable(W)
    W = coxeter('C', 2)
    somechecks.append(checksh(W, [v**2, v]))
    chartable(W)
    W = coxeter('C', 3)
    chartable(W)
    W = coxeter('C', 4)
    t = chartable(W)
    somechecks.append(checksh(W, v))
    somechecks.append(ainvariants(W, 1) == t['a'])
    W = coxeter('C', 5)
    chartable(W)
    W = coxeter('D', 4)
    somechecks.append(checksh(W, v))
    t = chartable(W)
    somechecks.append(ainvariants(W, 1) == t['a'])
    W = coxeter('D', 5)
    t = chartable(W)
    # somechecks.append(ainvariants(W, 1)==t['a'])
    W = coxeter('D', 6)
    W = coxeter('D', 7)
    W = coxeter('D', 8)
    W = coxeter('G', 2)
    chartable(W)
    somechecks.append(checksh(W, [v**2, v]))
    W = coxeter('I5', 2)
    chartable(W)
    somechecks.append(checksh(W, v))
    somechecks.append(sum(x[1] for x in specialpieces(W, v)) == v**(2 * W.N))
    W = coxeter('F', 4)
    t = chartable(W)
    somechecks.append(ainvariants(W, 1) == t['a'])
    somechecks.append(checksh(W, [v**2, v**2, v, v]))
    somechecks.append(sum(x[1] for x in specialpieces(W, v)) == v**(2 * W.N))
    W = coxeter('I5', 2)
    chartable(W)
    W = coxeter('H', 3)
    chartable(W)
    somechecks.append(checksh(W, v))
    W = coxeter('H', 4)
    chartable(W)
    W = coxeter('E', 6)
    t = chartable(W)
    # somechecks.append(ainvariants(W, 1)==t['a'])
    somechecks.append(checksh(W, v))
    W = coxeter('E', 7)
    chartable(W)
    W = coxeter('E', 8)
    chartable(W)
    W = coxeter(affinecartanmat("A", 1))
    W = coxeter(affinecartanmat("A", 2))
    W = coxeter(affinecartanmat("A", 3))
    W = coxeter(affinecartanmat("A", 4))
    W = coxeter(affinecartanmat("B", 3))
    W = coxeter(affinecartanmat("B", 4))
    W = coxeter(affinecartanmat("B", 5))
    W = coxeter(affinecartanmat("C", 2))
    W = coxeter(affinecartanmat("C", 3))
    W = coxeter(affinecartanmat("C", 4))
    W = coxeter(affinecartanmat("D", 4))
    W = coxeter(affinecartanmat("D", 5))
    W = coxeter(affinecartanmat("D", 6))
    W = coxeter(affinecartanmat("G", 2))
    W = coxeter(affinecartanmat("F", 4))
    W = coxeter(affinecartanmat("E", 6))
    W = coxeter(affinecartanmat("E", 7))
    W = coxeter(affinecartanmat("E", 8))
    # mixed finite and affine type:
    W = coxeter([[2, 0, -3, 0, 0, 0], [0, 2, -1, 0, 0, 0], [-1, -1, 2, 0, 0, 0],
               [0, 0, 0, 2, -1, 0], [0, 0, 0, -1, 2, -1], [0, 0, 0, 0, -1, 2]])
    lprint(str(W.cartantype) + '\n')
    lprint(str(W.cartanname) + '\n')
    # check all functions on this example:
    W = coxeter([[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -2],
                 [0, 2, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1, 0],
                 [0, 0, 2, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
                 [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
                 [0, 0, 0, 0, 2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, 2, -1, 0, 0, 0, -1, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, -1, 2, 0, 0, 0, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, 0, 0, 2, 0, -1, -1, 0, 0, 0, 0],
                 [0, -1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
                 [0, 0, -1, 0, -1, 0, 0, -1, 0, 2, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 2, 0, 0, 0, 0],
                 [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
                 [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
                 [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
                 [-1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]])
    lprint(str(W.cartantype) + '\n')
    lprint(str(W.cartanname) + '\n')
    lprint(str(W.order) + '\n')
    somechecks.append(W.cartan == cartantypetomat(cartantotype(W.cartan)))
    c = conjugacyclasses(W)
    r = reflections(W)
    l = longestperm(W)
    a = allelmchain(W)
    H = reflectionsubgroup(W, [0, 1, 2, 3, 4, 5, 6, 7, W.N - 1])
    lH = H.permtoword(longestperm(H))
    lW = H.reducedword(lH, W)
    W = coxeter([[2, 0, -1, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, -1, 0, 0, 0, 0],
        [-2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, -1, 0, -1, 0, 0], [0, -1, 0, -1, 2, 0, 0, -1, 0],
        [0, 0, 0, 0, 0, 2, 0, 0, -1], [0, 0, 0, -1, 0, 0, 2, 0, 0], [0, 0, 0, 0, -1, 0, 0, 2, 0],
        [0, 0, 0, 0, 0, -3, 0, 0, 2]])
    lprint(str(W.cartantype) + '\n')
    lprint(str(W.cartanname) + '\n')
    lprint(str(W.order) + '\n')
    somechecks.append(W.cartan == cartantypetomat(cartantotype(W.cartan)))
    cl = conjugacyclasses(W)
    H = reflectionsubgroup(W, [0, 1, 2, 3, 4, 5, 6, 7, W.N - 1])
    # test embedding of reflections
    W = coxeter("F", 4)
    c = coxeterclasses(W)
    rw = [W.coxelmtoword(r) for r in reflections(W)]
    for r in range(W.N):
        H = reflectionsubgroup(W, [r])
        somechecks.append(rw[r] == H.reducedword([0], W))
    somechecks.append(ainvariants(W, 1) == chartable(W)['a'])
    W = coxeter(affinecartanmat("F", 4))
    a = [[W.mattoword(m) for m in l] for l in allmats(W, 3)]
    W = coxeter("E", 8)
    c = coxeterclasses(W)
    e = allelmchain(W)
    W.coxelmlength(longestperm(W))
    H = reflectionsubgroup(W, [0, 1, 2, 3, 4, 5, 6])
    f = fusionconjugacyclasses(H, W)
    t = inductiontable(H, W)
    lprint('# ==>  looks good ... \n')
    W = coxeter("H", 4)
    f = lusztigfamilies(W, 1)
    somechecks.append(ainvariants(W, 1) == chartable(W)['a'])
    c = coxeterclasses(W)
    c1 = conjugacyclasses(W)
    e = allelmchain(W)
    d = redleftcosetreps(W, [0, 1, 2])
    # ca=redleftcosetreps(W)
    # wa=[W.coxelmtoword(c) for c in ca]
    # ls=[W.coxelmlength(c) for c in ca]    # does not work
    lprint('# ==>  seems ok ! ... \n')
    # somechecks.append(ca==[W.wordtocoxelm(w) for w in wa])
    W = coxeter("B", 3)
    lc = []
    for i in range(4):
        kl = klpolynomials(W, [i, 1, 1, 1], v)
        lc.append(len(kl['lcells']))
    somechecks.append(lc == [10, 14, 16, 20])
    k = [i.matrices(True) for i in klcells(W, 1, v)[1]]
    somechecks.append(all(isinstance(m, list) for m in k))
    k = [i.matrices(True) for i in klcells(W, [3, 2, 2], v)]
    somechecks.append(all(isinstance(m, list) for m in k))
    W = coxeter("I14", 2)
    k = [i.matrices(True) for i in klcells(W, 1, v)[1]]
    somechecks.append(all(isinstance(m, list) for m in k))
    k = [i.matrices(True) for i in klcells(W, [5, 3], v)]
    somechecks.append(all(isinstance(m, list) for m in k))
    # test all conversions:
    W = coxeter("H", 3)
    somechecks.append(cellrepcheck1(W, klcellreps(W)))
    somechecks.append(cellrepcheck2(W))
    gh3 = [[[]], [[0], [0, 1, 0]], [[0, 1, 0, 2, 1, 0]],
           [[0, 1, 0, 1, 2, 1, 0, 1, 0], [0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0]],
           [[0, 1, 0, 1, 0]], [[0, 1, 0, 1, 0, 2, 1, 0, 1, 0], [0, 1, 0, 1, 0, 2, 1, 0,
                                                                1, 0, 2, 1, 0, 1]],
           [[0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2]], [[0, 2]],
           [[0, 1, 2, 1, 0],
            [0, 1, 2, 1, 0, 1, 0, 2]], [[0, 2, 1, 0, 1, 0, 2]], [[0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0]],
           [[0, 1,
             2, 1, 0, 1, 0, 2, 1, 0, 1, 2], [0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2]],
           [[1], [1, 0, 1]], [[1,
                               0, 2, 1]], [[1, 0, 1, 2, 1, 0, 1], [1, 0, 1, 2, 1, 0, 1, 0, 2, 1]],
           [[1, 0, 1, 0, 2, 1, 0, 1]],
           [[1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1]], [[1, 2, 1], [1, 2, 1, 0, 1, 2]],
           [[1, 0, 2, 1, 0, 1, 0,
             2, 1]], [[1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2], [1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2]],
           [[2],
            [2, 1, 0, 1, 2]], [[2, 1, 0, 1, 0, 2, 1, 0, 1, 2]]]
    cl = allclasspolynomials(W, v**2)
    l = []
    for x in gh3:
        y = leftcellleadingcoeffs(W, 1, v, x, cl)
        l.append(y['ti'])
    somechecks.append(l == [[[('1_r',), [1]]], [[("3_s'",), [1, ir5]],
       [("overline{3}_s'",), [1, 1 - ir5]]], [[('5_r',), [1]]],
       [[("4_r'",), [1, 1]], [('4_r',), [1, -1]]], [[("5_r'",), [1]]],
       [[('3_s',), [ir5, 1]], [('overline{3}_s',), [1 - ir5, 1]]],
       [[("1_r'",), [1]]], [[('5_r',), [1]]], [[("4_r'",), [1, 1]],
       [('4_r',), [1, -1]]], [[("5_r'",), [1]]], [[("5_r'",), [1]]],
       [[('3_s',), [ir5, 1]], [('overline{3}_s',), [1 - ir5, 1]]],
       [[("3_s'",), [1, ir5]], [("overline{3}_s'",), [1, 1 - ir5]]],
       [[('5_r',), [1]]], [[("4_r'",), [1, 1]], [('4_r',), [1, -1]]],
       [[('5_r',), [1]]], [[("5_r'",), [1]]], [[("4_r'",), [1, 1]],
       [('4_r',), [1, -1]]], [[("5_r'",), [1]]], [[('3_s',), [ir5, 1]],
       [('overline{3}_s',), [1 - ir5, 1]]], [[("3_s'",), [1, ir5]],
       [("overline{3}_s'",), [1, 1 - ir5]]], [[('5_r',), [1]]]])
    c = allcellsleadingcoeffs(W, 1, v)
    c = constructible(W, 1)
    ah = redleftcosetreps(W)
    ap = [W.coxelmtoperm(c) for c in ah]
    aw = [W.coxelmtoword(c) for c in ah]
    am = [W.coxelmtomat(c) for c in ah]
    alc = [W.coxelmlength(c) for c in ah]
    alm = [W.matlength(m) for m in am]
    somechecks.append(alc == [len(w) for w in aw])
    somechecks.append(alc == alm)
    somechecks.append(ah == [c[:len(W.rank)] for c in ap])
    somechecks.append(am == [W.coxelmtomat(c) for c in ah])
    somechecks.append(aw == [W.coxelmtoword(c) for c in ah])
    somechecks.append(aw == [W.permtoword(c) for c in ap])
    somechecks.append(ap == [W.coxelmtoperm(c) for c in ah])
    somechecks.append(ap == [W.mattoperm(m) for m in am])
    somechecks.append(ah == [W.mattocoxelm(m) for m in am])
    somechecks.append(aw == [W.mattoword(m) for m in am])
    somechecks.append(ah == [W.wordtocoxelm(w) for w in aw])
    somechecks.append(am == [W.wordtomat(w) for w in aw])
    somechecks.append(ap == [W.wordtoperm(w) for w in aw])
    somechecks.append(aw == [W.reducedword(w, W) for w in aw])
    aa = allwords(W)
    somechecks.append(all(w in aa for w in aw))
    aa = [W.stringtoword(x) for x in allwordstrings(W)]
    somechecks.append(all(w in aa for w in aw))
    w = W.wordtoperm([0, 1, 0, 2])
    b1 = list(filter(lambda x: bruhatcoxelm(W, x, w), ah))
    b1a = list(filter(lambda x: bruhat(W, x, w), ah))
    elms = [W.coxelmtoperm(c) for c in ah]
    b2 = list(filter(lambda x: bruhatperm(W, x, w), elms))
    b2a = list(filter(lambda x: bruhat(W, x, w), elms))
    mats = [W.coxelmtomat(c) for c in ah]
    somechecks.append([W.coxelmtoword(p)
                       for p in b2] == [W.coxelmtoword(p) for p in b1])
    somechecks.append([W.coxelmtoword(p)
                       for p in b2a] == [W.coxelmtoword(p) for p in b1a])
    W = coxeter('F', 4)
    lusztigfamilies(W, 0)
    lusztigfamilies(W, 1)
    lusztigfamilies(W, [3, 3, 2, 2])
    lusztigfamilies(W, [2, 2, 1, 1])
    constructible(W, [2, 2, 1, 1])
    lusztigfamilies(W, [3, 3, 1, 1])
    lprint('#I ')
    p = [3, 2, 1, 0]
    nc = [[W.cartan[i][j] for j in p] for i in p]
    somechecks.append(nc == cartantypetomat(cartantotype(nc)))
    aa = redleftcosetreps(W)
    w1 = [0, 2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]
    lb4 = []
    for l in range(1, 21):
        l1 = len(list(filter(lambda x: bruhatperm(W, W.coxelmtoperm(x),
                                                  W.wordtoperm(w1[:l])), aa)))
        lb4.append(l1)
        lprint(str(l1) + ' ')
    lprint('\n')
    somechecks.append(lb4 == [2, 4, 8, 12, 20, 40, 60, 96, 132, 196, 244, 272,
                              396, 456, 508, 680, 720, 828, 912, 972])
    b5 = list(filter(lambda x: W.coxelmlength(x) <= len(w1), aa))
    somechecks.append(len(b5) == 1122)
    somechecks.append(cellrepcheck1(W, klcellreps(W)))
    somechecks.append(cellrepcheck2(W))
    W = coxeter("D", 4)
    somechecks.append(cellrepcheck1(W, klcellreps(W)))
    somechecks.append(cellrepcheck2(W))
    W = coxeter("E", 7)
    somechecks.append(cellrepcheck1(W, klcellreps(W)))
    lprint('###############################################\n')
    lprint('# ' + str(len(somechecks)) + ' true/false checks performed ')
    if not all(somechecks):
        lprint(' ==> !!! There are problems !!!\n')
    else:
        lprint(' ==> Tests ok\n')
    lprint('###############################################\n')
    return all(somechecks)
