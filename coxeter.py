from functools import reduce

from polynomials import ir, rootof1
from matrices import (permmult, perminverse, decomposemat, flatlist,
                      matmult, cartesian,
                      intlcmlist,
                      directsummat, idmat,
                      determinantmat, gcdex,
                      partitiontuples, centralisertuple, centraliserpartition,
                      partitions)


def cartanmatA(n):
    """
    Cartan matrix of type A as a list of lists.

    >>> cartanmatA(2)
    [[2, -1], [-1, 2]]
    """
    if n == 0:
        return [[]]
    a = [[2 if i == j else 0 for i in range(n)] for j in range(n)]
    for i in range(n - 1):
        a[i][i + 1] = -1
        a[i + 1][i] = -1
    return a


def cartanmat(typ, n):
    r"""returns a Cartan matrix (of finite Dynkin type) where typ is
    a string specifying  the type.  The  convention is such that
    the (i,j)-entry of this matrix equals::

                  (e_i,e_j)
                2 ---------
                  (e_i,e_i)

    where  e_0, e_1, ... are the  simple  roots and  ( , ) is an
    invariant bilinear form.  (This is the same convention as in
    gap-chevie.)

    See also 'affinecartanmat', 'directsummat' and 'cartantotype'.

    >>> cartanmat("A",2)
    [[2, -1], [-1, 2]]
    >>> cartanmat("B",3)               # diagram    0 <= 1 -- 2
    [[2, -2, 0], [-1, 2, -1], [0, -1, 2]]
    >>> cartanmat("C",3)               # diagram    0 => 1 -- 2
    [[2, -1, 0], [-2, 2, -1], [0, -1, 2]]
    >>> cartanmat("I5",2)
    [[2, -ir5], [-ir5, 2]]

    See 'zeta5' for the definition of ir5.

    The complete list of the graphs  with their labelling is as
    follows::

             0   1   2          n-1               0   1   2          n-1
       A_n   o---o---o-- . . . --o          B_n   o=<=o---o-- . . . --o

           1 o
              \    3            n-1               0   1   2          n-1
       D_n   2 o---o---  . . . --o          C_n   o=>=o---o-- . . . --o
              /
           0 o

             0   1             0   1   2   3          0   2   3   4   5
       G_2   0->-0        F_4  o---o=>=o---o     E_6  o---o---o---o---o
               6                                              |
                                                              o 1

             0   2   3   4   5   6            0   2   3   4   5   6   7
       E_7   o---o---o---o---o---o       E_8  o---o---o---o---o---o---o
                     |                                |
                     o 1                              o 1

                 0   1                 0   1   2          0   1   2   3
       I_2(m)    o->-o            H_3  o---o---o     H_4  o---o---o---o
                   m                     5                  5

    """
    if typ[0] == 'A':
        return cartanmatA(n)
    if typ[0] == 'B':
        a = cartanmatA(n)
        if n >= 2:
            a[0][1] = -2
        return a
    if typ[0] == 'C':
        a = cartanmatA(n)
        if n >= 2:
            a[1][0] = -2
        return a
    if typ[0] == 'D':
        if n == 2:
            return [[2, 0], [0, 2]]
        if n >= 3:
            a = cartanmatA(n)
            a[0][1] = 0
            a[0][2] = -1
            a[1][0] = 0
            a[1][2] = -1
            a[2][0] = -1
            a[2][1] = -1
            return a
    if typ[0] == 'G':
        return [[2, -1],
                [-3, 2]]
    if typ[0] == 'F':
        return [[2, -1, 0, 0],
                [-1, 2, -1, 0],
                [0, -2, 2, -1],
                [0, 0, -1, 2]]
    if typ[0] == 'E' and n == 6:
        return [[2, 0, -1, 0, 0, 0],
                [0, 2, 0, -1, 0, 0],
                [-1, 0, 2, -1, 0, 0],
                [0, -1, -1, 2, -1, 0],
                [0, 0, 0, -1, 2, -1],
                [0, 0, 0, 0, -1, 2]]
    if typ[0] == 'E' and n == 7:
        return [[2, 0, -1, 0, 0, 0, 0],
                [0, 2, 0, -1, 0, 0, 0],
                [-1, 0, 2, -1, 0, 0, 0],
                [0, -1, -1, 2, -1, 0, 0],
                [0, 0, 0, -1, 2, -1, 0],
                [0, 0, 0, 0, -1, 2, -1],
                [0, 0, 0, 0, 0, -1, 2]]
    if typ[0] == 'E' and n == 8:
        return [[2, 0, -1, 0, 0, 0, 0, 0],
                [0, 2, 0, -1, 0, 0, 0, 0],
                [-1, 0, 2, -1, 0, 0, 0, 0],
                [0, -1, -1, 2, -1, 0, 0, 0],
                [0, 0, 0, -1, 2, -1, 0, 0],
                [0, 0, 0, 0, -1, 2, -1, 0],
                [0, 0, 0, 0, 0, -1, 2, -1],
                [0, 0, 0, 0, 0, 0, -1, 2]]
    if typ[0] == 'H' and n == 3:
        return [[2, -ir(5), 0],
                [-ir(5), 2, -1],
                [0, -1, 2]]
    if typ[0] == 'H' and n == 4:
        return [[2, -ir(5), 0, 0],
                [-ir(5), 2, -1, 0],
                [0, -1, 2, -1],
                [0, 0, -1, 2]]
    if typ[0] == 'I':
        m = int(typ[1:])
        if m % 2 == 0:
            if m == 4:
                return [[2, -1], [-2, 2]]
            if m == 6:
                return [[2, -1], [-3, 2]]
            return [[2, -1], [-2 - ir(m // 2), 2]]
        else:
            if m == 3:
                return [[2, -1], [-1, 2]]
            if m == 5:
                return [[2, -ir(m)], [-ir(m), 2]]
            d = gcdex(2 + m, 2 * m)['coeff1']
            z = rootof1(m)
            if d % 2 == 0:
                z1 = -z**d - z**(-d)
            else:
                z1 = z**d + z**(-d)
            return [[2, z1], [z1, 2]]


def affinecartanmat(typ, n):
    """returns a generalised Cartan matrix of affine type, where typ
    is a string specifying the corresponding finite type.

    >>> affinecartanmat("A",1)
    [[2, -2], [-2, 2]]
    >>> affinecartanmat("G",2)     # diagram  0 -- 1 >= 2
    [[2, -1, 0],
     [-1, 2, -1],
     [0, -3, 2]]
    >>> affinecartanmat("F",4)     # diagram  4 -- 0 -- 1 => 2 -- 3
    [[2, -1, 0, 0, -1],
     [-1, 2, -1, 0, 0],
     [0, -2, 2, -1, 0],
     [0, 0, -1, 2, 0],
     [-1, 0, 0, 0, 2]]
    >>> affinecartanmat("B",3)     # diagram  0 <= 2 -- 3
    [[2, -2, 0, 0],
     [-1, 2, -1, -1],
     [0, -1, 2, 0],
     [0, -1, 0, 2]]
    >>> affinecartanmat("C",3)     # diagram  0 => 1 -- 2 <= 3
    [[2, -1, 0, 0],
     [-2, 2, -1, 0],
     [0, -1, 2, -2],
     [0, 0, -1, 2]]

    See also 'cartanmat'.
    """
    a = cartanmat(typ, n + 1)
    if typ[0] == 'A' and n == 1:
        a[0][1] = -2
        a[1][0] = -2
        return a
    if typ[0] == 'A' and n >= 2:
        a[0][n] = -1
        a[n][0] = -1
        return a
    if typ[0] == 'B' and n >= 3:
        a[n - 1][n] = 0
        a[n][n - 1] = 0
        a[n - 2][n] = -1
        a[n][n - 2] = -1
        return a
    if typ[0] == 'C' and n >= 2:
        a[n - 1][n] = -2
        a[n][n - 1] = -1
        return a
    if typ[0] == 'D' and n >= 4:
        a[n - 1][n] = 0
        a[n][n - 1] = 0
        a[n - 2][n] = -1
        a[n][n - 2] = -1
        return a
    if typ[0] == 'G':
        return [[2, -1, 0],
                [-1, 2, -1],
                [0, -3, 2]]
    if typ[0] == 'F':
        return [[2, -1, 0, 0, -1],
                [-1, 2, -1, 0, 0],
                [0, -2, 2, -1, 0],
                [0, 0, -1, 2, 0],
                [-1, 0, 0, 0, 2]]
    if typ[0] == 'E' and n == 6:
        return [[2, 0, -1, 0, 0, 0, 0],
                [0, 2, 0, -1, 0, 0, -1],
                [-1, 0, 2, -1, 0, 0, 0],
                [0, -1, -1, 2, -1, 0, 0],
                [0, 0, 0, -1, 2, -1, 0],
                [0, 0, 0, 0, -1, 2, 0],
                [0, -1, 0, 0, 0, 0, 2]]
    if typ[0] == 'E' and n == 7:
        return [[2, 0, -1, 0, 0, 0, 0, -1],
                [0, 2, 0, -1, 0, 0, 0, 0],
                [-1, 0, 2, -1, 0, 0, 0, 0],
                [0, -1, -1, 2, -1, 0, 0, 0],
                [0, 0, 0, -1, 2, -1, 0, 0],
                [0, 0, 0, 0, -1, 2, -1, 0],
                [0, 0, 0, 0, 0, -1, 2, 0],
                [-1, 0, 0, 0, 0, 0, 0, 2]]
    if typ[0] == 'E' and n == 8:
        return [[2, 0, -1, 0, 0, 0, 0, 0, 0],
                [0, 2, 0, -1, 0, 0, 0, 0, 0],
                [-1, 0, 2, -1, 0, 0, 0, 0, 0],
                [0, -1, -1, 2, -1, 0, 0, 0, 0],
                [0, 0, 0, -1, 2, -1, 0, 0, 0],
                [0, 0, 0, 0, -1, 2, -1, 0, 0],
                [0, 0, 0, 0, 0, -1, 2, -1, 0],
                [0, 0, 0, 0, 0, 0, -1, 2, -1],
                [0, 0, 0, 0, 0, 0, 0, -1, 2]]


def typecartanmat(mat):
    """identifies the type of an indecomposable Cartan matrix.
    """
    n = len(mat[0])
    if n == 0:
        return ['A', []]
    if n == 1:
        return ['A', [0]]
    if n == 2:
        if mat[0][1] * mat[1][0] < 4:
            if mat[1][0] == -3:
                return ['G', [0, 1]]
            if mat[0][1] == -3:
                return ['G', [1, 0]]
            if mat[1][0] == -2:
                return ['C', [0, 1]]
            if mat[0][1] == -2:
                return ['C', [1, 0]]
            if mat[0][1] == -1 and mat[1][0] == -1:
                return ['A', [0, 1]]
            if mat[0][1] == -ir(5) and mat[1][0] == -ir(5):
                return ['I5', [0, 1]]
            # m=3
            # while mat[0][1]!=-ir(m): m+=1
            p = [[-1, mat[0][1]], [-mat[1][0], mat[0][1] * mat[1][0] - 1]]
            p1 = [[-1, mat[0][1]], [-mat[1][0], mat[0][1] * mat[1][0] - 1]]
            m = 1
            while p1[0][0] != 1 or p1[0][1] != 0 or p1[1][0] != 0 or p1[1][1] != 1:
                p1 = matmult(p1, p)
                m += 1
            if m % 2 == 0 and mat[1][0] == -1:
                return ['I' + str(m), [1, 0]]
            else:
                return ['I' + str(m), [0, 1]]
        else:
            return ['U', [0, 1]]
    else:
        typ = ['A', 'B', 'C', 'D']
        cs = [cartanmat('A', n), cartanmat('B', n),
              cartanmat('C', n), cartanmat('D', n)]
        if n == 3:
            typ.append('H')
            cs.append(cartanmat('H', 3))
        if n == 4:
            typ.append('F')
            cs.append(cartanmat('F', 4))
            typ.append('H')
            cs.append(cartanmat('H', 4))
        if n == 6:
            typ.append('E')
            cs.append(cartanmat('E', 6))
        if n == 7:
            typ.append('E')
            cs.append(cartanmat('E', 7))
        if n == 8:
            typ.append('E')
            cs.append(cartanmat('E', 8))
        if mat in cs:
            return [typ[cs.index(mat)], list(range(n))]
        nb = [[j for j in range(n) if i != j and mat[i][j] != 0] for i in range(n)]
        es = [i for i in range(n) if len(nb[i]) == 1]   # end nodes
        if not es:     # circle
            return ['U', list(range(n))]
        elif len(es) == 2:   # straight line
            p = [es[0]]
            for s in p:
                for j in nb[s]:
                    if j not in p:
                        p.append(j)
            a = [[mat[i][j] for j in p] for i in p]
            if a in cs:
                return [typ[cs.index(a)], p]
            else:
                p.reverse()
                a = [[mat[i][j] for j in p] for i in p]
                if a in cs:
                    return [typ[cs.index(a)], p]
                else:
                    return ["U", list(range(n))]
        elif len(es) == 3:    # three end nodes
            p0 = [es[0]]
            for s in p0:
                if len(nb[s]) != 3:
                    for j in nb[s]:
                        if j not in p0:
                            p0.append(j)
            p1 = [es[1]]
            for s in p1:
                if len(nb[s]) != 3:
                    for j in nb[s]:
                        if j not in p1:
                            p1.append(j)
            p2 = [es[2]]
            for s in p2:
                if len(nb[s]) != 3:
                    for j in nb[s]:
                        if j not in p2:
                            p2.append(j)
            ps = [p0, p1, p2]
            lp = [len(p0), len(p1), len(p2)]   # branch lengths
            lp1 = lp[:]
            lp1.sort()
            p = n * [0]
            if lp1 == [2, 2, n - 2]:  # type D or affB
                typ = 'D'
                if n == 4:
                    r = 1    # like this it fits with embedding of D in B
                else:
                    r = lp.index(n - 2)
                for i in range(n - 2):
                    p[i + 2] = ps[r][-i - 1]
                l1 = [0, 1, 2]
                l1.remove(r)
                p[0] = ps[l1[0]][0]
                p[1] = ps[l1[1]][0]
                if not [[mat[i][j] for j in p] for i in p] in cs:  # testing
                    return ["U", list(range(n))]
                return [typ, p]
            elif lp1 in [[2, 3, 3], [2, 3, 4], [2, 3, 5]]:  # type E
                typ = 'E'
                r2 = lp.index(2)
                r3 = lp.index(3)
                p[0] = ps[r3][0]
                p[2] = ps[r3][1]
                p[1] = ps[r2][0]
                l1 = [0, 1, 2]
                l1.remove(r2)
                l1.remove(r3)
                r = l1[0]
                for i in range(len(ps[r])):
                    p[i + 3] = ps[r][-i - 1]
                if not [[mat[i][j] for j in p] for i in p] in cs:  # testing
                    return ["U", list(range(n))]
                return [typ, p]
            else:
                return ["U", list(range(n))]
        else:
            return ["U", list(range(n))]


def finitetypemat(mat):
    """identifies the type of an indecomposable Cartan matrix, which
    is assumed to be of finite type.
    """
    n = len(mat[0])
    if n == 0:
        return ['A', []]
    if n == 1:
        return ['A', [0]]
    if n == 2:
        if mat[1][0] == -3:
            return ['G', [0, 1]]
        if mat[0][1] == -3:
            return ['G', [1, 0]]
        if mat[1][0] == -2:
            return ['C', [0, 1]]
        if mat[0][1] == -2:
            return ['C', [1, 0]]
        if mat[0][1] == -1 and mat[1][0] == -1:
            return ['A', [0, 1]]
        if mat[0][1] == -ir(5) and mat[1][0] == -ir(5):
            return ['I5', [0, 1]]
        m = 3
        while mat[0][1] != -ir(m):
            m += 1
        return ['I' + str(m), [0, 1]]
    else:
        rowsums = [sum(l) for l in mat]
        nb = [[j for j in range(n) if i != j and mat[i][j] != 0] for i in range(n)]
        es = [i for i in range(n) if len(nb[i]) == 1]   # end nodes
        if len(es) == 2:   # straight line
            p = [es[0]]
            for s in p:
                for j in nb[s]:
                    if j not in p:
                        p.append(j)
            totsum = sum(rowsums)
            if totsum == 2:
                return ['A', p]
            elif totsum < 1:
                if mat[p[0]][p[1]] != -1:
                    return ['H', p]
                else:
                    p.reverse()
                    return ['H', p]
            else:    # totsum 1
                if mat[p[2]][p[1]] == -2:
                    return ['F', p]
                if mat[p[1]][p[2]] == -2:
                    p.reverse()
                    return ['F', p]
                if -1 in rowsums:  # type C
                    if mat[p[1]][p[0]] == -2:
                        return ['C', p]
                    else:
                        p.reverse()
                        return ['C', p]
                else:
                    if mat[p[0]][p[1]] == -2:
                        return ['B', p]
                    else:
                        p.reverse()
                        return ['B', p]
        else:    # three end nodes
            p0 = [es[0]]
            for s in p0:
                if len(nb[s]) != 3:
                    for j in nb[s]:
                        if j not in p0:
                            p0.append(j)
            p1 = [es[1]]
            for s in p1:
                if len(nb[s]) != 3:
                    for j in nb[s]:
                        if j not in p1:
                            p1.append(j)
            p2 = [es[2]]
            for s in p2:
                if len(nb[s]) != 3:
                    for j in nb[s]:
                        if j not in p2:
                            p2.append(j)
            ps = [p0, p1, p2]
            lp = [len(p0), len(p1), len(p2)]   # branch lengths
            lp1 = lp[:]
            lp1.sort()
            p = n * [0]
            if lp1 == [2, 2, n - 2]:  # type D or affB
                typ = 'D'
                if n == 4:
                    r = 1    # like this it fits with embedding of D in B
                else:
                    r = lp.index(n - 2)
                for i in range(n - 2):
                    p[i + 2] = ps[r][-i - 1]
                l1 = [0, 1, 2]
                l1.remove(r)
                p[0] = ps[l1[0]][0]
                p[1] = ps[l1[1]][0]
                return [typ, p]
            elif lp1 in [[2, 3, 3], [2, 3, 4], [2, 3, 5]]:  # type E
                typ = 'E'
                r2 = lp.index(2)
                r3 = lp.index(3)
                p[0] = ps[r3][0]
                p[2] = ps[r3][1]
                p[1] = ps[r2][0]
                l1 = [0, 1, 2]
                l1.remove(r2)
                l1.remove(r3)
                r = l1[0]
                for i in range(len(ps[r])):
                    p[i + 3] = ps[r][-i - 1]
                return [typ, p]


def cartantotype(mat):
    """returns [['U',range(n)]] if mat is a  generalised Cartan matrix
    which is  not of  finite type, where n is the rank.  Otherwise,
    the function returns a sequence of pairs  (typ,l)  where typ is
    a string (Cartan type)  and l  is a list of integers  such that

       [[mat[i][j] for j in l] for i in l]==cartanmat(typ,len(l))

    (exactly as in  gap-chevie). Thus, for finite types, the Cartan
    matrix is uniquely determined by the result of cartantotype.

    >>> cartantotype([[ 2, 0,-1, 0, 0],
    ...               [ 0, 2, 0,-3, 0],
    ...               [-2, 0, 2, 0,-1],
    ...               [ 0,-1, 0, 2, 0],
    ...               [ 0, 0,-1, 0, 2]])
    [['C', [0, 2, 4]], ['G', [3, 1]]]
    >>> cartantotype([[ 2, -2], [-2, 2]])
    [['U', [0, 1]]]

    See also 'cartantypetomat'.
    """
    if mat == [[]]:
        return [['A', []]]

    l = decomposemat(mat)
    t = []
    for l1 in l:
        c = typecartanmat([[mat[i][j] for j in l1] for i in l1])
        t.append([c[0], [l1[i] for i in c[1]]])
        if c[0][0] == 'U':      # not of finite type: exit
            return [['U', list(range(len(mat[0])))]]
    t.sort()
    t.sort(key=(lambda x: len(x[1])), reverse=True)  # sort as in gap-chevie
    for c, li in t:  # testing
        if c[0] != 'U' and c[0] != 'I':
            if [[mat[i][j] for j in li]
                    for i in li] != cartanmat(c, len(li)):
                raise ValueError('something went wrong')
    return t


def cartantypetomat(ct):
    """reconstructs the  Cartan matrix from its cartan type, if ct
    corresponds to a list of finite type Cartan matrices. Thus,
    if c is a Cartan matrix of finite type, then

          c==cartantypetomat(cartantotype(c)).

    This function only works for finite type.

    >>> cartantypetomat([['C',[0,2,4]],['G',[3,1]]])
    [[2, 0, -1, 0, 0],
     [0, 2, 0, -3, 0],
     [-2, 0, 2, 0, -1],
     [0, -1, 0, 2, 0],
     [0, 0, -1, 0, 2]]
    """
    b = [[]]
    p = []
    for c, li in ct:
        b = directsummat(b, cartanmat(c, len(li)))
        p.extend(li)
    n = range(len(p))
    return [[b[p.index(i)][p.index(j)] for j in n] for i in n]


def degreesdata(typ, n):
    """returns  the reflection degrees of the finite Coxeter group
    of type 'typ'  and rank 'n'.  The data  are taken from  the
    corresponding files in  gap-chevie.  By  Solomon's Theorem,
    the degrees  d_1, ..., d_r  (where r is the rank of W)  are
    determined by the equation::

                                         u^{d_i}-1
        sum_{w in W} u^{l(w)} = prod_i  ----------
                                            u-1

    where i runs over 1, ..., r.  In particular, the product of
    all degrees is the order of W. -- When 'coxeter' is called,
    the resulting python class will have a component 'degrees'.
    (If W is not irreducible, the degrees of W are the disjoint
    union of the degrees of the irreducible components of W.)

    >>> W = coxeter("H",3)
    >>> W.degrees
    [2, 6, 10]
    >>> W.order
    120

    See also 'coxeter'.
    """
    if typ[0] == 'G':
        return [2, 6]
    if typ[0] == 'F':
        return [2, 6, 8, 12]
    if typ[0] == 'E' and n == 6:
        return [2, 5, 6, 8, 9, 12]
    if typ[0] == 'E' and n == 7:
        return [2, 6, 8, 10, 12, 14, 18]
    if typ[0] == 'E' and n == 8:
        return [2, 8, 12, 14, 18, 20, 24, 30]
    if typ[0] == 'A':
        return [i + 2 for i in range(n)]
    if typ[0] == 'B' or typ[0] == 'C':
        return [2 * (i + 1) for i in range(n)]
    if typ[0] == 'D':
        l = [2 * (i + 1) for i in range(n)]
        l[-1] = n
        return l
    if typ[0] == 'H' and n == 3:
        return [2, 6, 10]
    if typ[0] == 'H' and n == 4:
        return [2, 12, 20, 30]
    if typ[0] == 'I':
        return [2, int(typ[1:])]

# F roots
# elms[i] applied to root[i] yields simple root (orbit rep)


def roots(cmat):
    rng = range(len(cmat[0]))
    gen = idmat(rng, 1)
    l1, elms, orbits = [], [], []
    while gen:
        orb = [gen[0][:]]
        orbe = [[]]
        i = 0
        while i < len(orb):
            for s in rng:
                nr = orb[i][:]
                nr[s] -= sum(cmat[s][t] * nr[t] for t in rng if cmat[s][t] != 0)
                if nr[s] >= 0 and nr not in orb:
                    orb.append(nr)
                    w = orbe[i][:]
                    w.append(s)
                    orbe.append(w[:])
            i += 1
        orbits.append(orb)
        gen = [s for s in gen if s not in orb]
        l1.extend(orb)
        elms.extend(orbe)
    l = [r[:] for r in l1]
    l.sort(reverse=True)
    l.sort(key=sum)
    return ([tuple(r) for r in l + [[-x for x in y] for y in l]],
            [elms[l1.index(r)][::-1] for r in l],
            [[l.index(r) for r in orb] for orb in orbits])


def roots1(cmat):
    rng = range(len(cmat[0]))
    l = idmat(rng, 1)
    elms = [[] for _ in rng]
    i = 0
    while i < len(l):
        for s in rng:
            nr = l[i][:]
            nr[s] -= sum(cmat[s][t] * nr[t] for t in rng if cmat[s][t] != 0)
            if nr[s] >= 0 and nr not in l:
                l.append(nr)
                w = elms[i][:]
                w.append(s)
                elms.append(w[:])
        i += 1
    l1 = [r[:] for r in l]
    l.sort(reverse=True)
    l.sort(key=sum)
    return ([tuple(r) for r in l + [[-x for x in y] for y in l]],
            [elms[l1.index(r)][::-1] for r in l])


def permroots(cmat, roots):
    rng = range(len(cmat[0]))
    gens = [len(roots) * [0] for s in rng]
    for s in rng:
        for i in range(len(roots)):
            nr = list(roots[i])
            nr[s] -= sum(cmat[s][t] * nr[t] for t in rng if cmat[s][t] != 0)
            gens[s][i] = roots.index(tuple(nr))
    return [tuple(s) for s in gens]


class coxeter:
    """creates a  Coxeter group (as a python 'class'), from a  Cartan
    matrix (see 'cartanmat') or from a pair (typ,r) where typ is a
    string specifying the type and r specifies the rank.

    >>> c = cartanmat("G",2); c
    [[2, -1], [-3, 2]]
    >>> W = coxeter(c)
    >>> W.N                             # number of positive roots
    6
    >>> W.roots                         # all roots
    [(1, 0), (0, 1), (1, 1), (1, 2), (1, 3), (2, 3),
     (-1, 0), (0, -1), (-1, -1), (-1, -2), (-1, -3), (-2, -3)]

    >>> W = coxeter("H",4); W.order
    14400

    Alternatively, the input may in fact be any generalised Cartan
    matrix, leading to an infinite Coxeter group in general.

    >>> W = coxeter([[2,0,-1,0],[0,2,0,-1],[-1,0,2,0],[0,-3,0,2]])
    >>> W.cartantype
    [['A', [0, 2]], ['G', [1, 3]]]

    >>> W = coxeter([[2,-2],[-2,2]]); W.cartantype
    [['U', [0, 1]]]

    Here the letter "U" denotes any non-finite type.

    If the  Cartan matrix is of  finite type, various more special
    methods are available  which  partly rely on  explicitly known
    information concerning finite Coxeter groups  (stored in files
    depending on this  module),  as in the  gap-chevie system; see

               http://www.math.rwth-aachen.de/~CHEVIE

    for further details. (While some knowledge  of  gap-chevie may
    be useful, it is not a prerequisite for using this program.)

    The result of 'coxeter' always has the following attributes:
      cartan            Cartan matrix (see also 'cartanmat')
      rank              list [0,...,r-1] where r is the rank
      coxetermat        Coxeter matrix
      cartantype        see 'cartantotype' for explanation
      cartanname        unique string identifying this group
      matgens           matrices of the simple reflections
      fusions           see 'reflectionsubgroup' for explanation
      weightL           see 'ainvariants' for explanation
      paramL            see 'heckechartable' for explanation

    If W is finite, there are further attributes:
      roots             full list of all roots (as in gap-chevie)
      N                 number of positive roots roots
      rootorbits        orbits of the action on the set of roots
      rootsorbits1      simple root representative for each root
      symform           relative root lengths (symmetrizes cartan)
      degrees           reflection degrees
      order             order of the group
      permgens          permutations of generators on all roots
      coxgens           effect on simple roots

    For finite Coxeter groups, the basic design features are taken
    over from gap-chevie, with the difference that (as  is  common
    in python) lists are indexed starting  with 0.  In particular:
    the roots are numbered from  0 to 2*W.N-1, where the first W.N
    roots are positive;  these  are followed by the  corresponding
    negative ones. We have for i in [0,..., W.N-1]:

       *  W.roots[W.N+i]=-W.roots[i]
       *  W.roots[i] lies in W-orbit of the k-th simple root
                                     where k=W.rootorbits1[i]

    Elements can be represented as reduced words, permutations  or
    matrices,  where we act from the right. (Thus,  row convention
    is used for matrices.) If w is given as a permutation and  s_i
    is the i-th simple reflection, then we have:

        l(s_iw)=l(w)+1  if and only if  w[i]<W.N.

    A word is simply  a list of  indices specifying the generators
    s_i.  In some occasions,  it  may be useful to  convert such a
    list into a string; this is conveniently done using the Python
    function 'join' (and its inverse 'split'):

    >>> w = '.'.join(str(i) for i in [0,1,4,3,2]); w
    '0.1.4.3.2'
    >>> [int(i) for i in w.split('.')]
    [0, 1, 4, 3, 2]

    A compact representation of  w in W  is given as follows.  For
    each i in W.rank,  let  r_i  be the  root obtained by applying
    w to the i-the simple root. Let a_i be the index of r_i in the
    list of roots; then w is uniquely determined by (a_1,...,a_r).
    Such tuples will be called 'coxelms'. For example,  the matrix
    of w (with respect to the basis given by the simple roots)  is
    the list [W.roots[a_1],...,W.roots[a_r]]. If p is the complete
    permutation representing w,  then the corresponding coxelm  is
    p[:len(W.rank)]. Several built-in functions (as python methods
    in W) convert between these formats. (In Python 3, we can also
    pack a list of 'coxelms' into a sequence of bytes; if the list
    of elements is long, a few  hundred thousands or millions say,
    then this way of storing requires roughly  r bytes per element
    where r is the rank of W.)

    For  infinite Coxeter groups,  elements are represented either
    by  matrices or  reduced words,  and  the conversion functions
    work in the general case.

    >>> W = coxeter("A",3)
    >>> w0 = longestperm(W);   print(w0)         # the longest element
    (8, 7, 6, 10, 9, 11, 2, 1, 0, 4, 3, 5)
    >>> W.permlength(w0)                         # the length of w
    6
    >>> W.coxelmtoword(w0)
    [0, 1, 0, 2, 1, 0]
    >>> W.reducedword([0,1,0,1,2,1,0],W)
    [1, 0, 2, 1, 0]

    >>> W = coxeter([[2,-2],[-2,2]]); W.cartantype
    [['U', [0, 1]]]
    >>> W.wordtomat([0,1,0,1,0,1,0,1,0,1])
    ((-9, -10), (10, 11))

    The optional argument weightL is a list of integers specifying
    a weight function in the sense of Lusztig. If the argument  is
    itself an integer, then all weights on simple reflections will
    be equal to that integer. The  default value is 0.  Similarly,
    the optional argument  param  specifies  the  parameter of the
    corresponding  Iwahori-Hecke  algebra; the default value is 1,
    in which case the Iwahori-Hecke algebra is a group algebra.

    The optional argument 'split' is a list defining a permutation
    of the generators such that the induced map is a Coxeter group
    automorphism. The default value is 'True' which corresponds to
    the identity automorphism.

    To see all available functions type 'help(allfunctions)'.

    For further theoretical background see Chapter 1 of

    [Ge-Pf] M. Geck and G. Pfeiffer, Characters of finite Coxeter
            groups and Iwahori-Hecke algebras, OUP, Oxford, 2000.
    """

    def __init__(self, typ, rank=0, split=True, fusion=[], weightL=0, param=1):
        if isinstance(typ, (tuple, list)):
            self.cartan = typ
            self.rank = list(range(len(typ[0])))
            self.cartantype = cartantotype(typ)
        else:
            self.cartan = cartanmat(typ, rank)
            self.rank = list(range(rank))
            if rank == 1:
                self.cartantype = [['A', [0]]]
            elif rank == 2 and typ == 'D':
                self.cartantype = [['A', [0]], ['A', [1]]]
            else:
                self.cartantype = [[typ, list(range(rank))]]
        if self.cartantype[0][0] == 'U':
            self.cartanname = 'U'
            for l in self.cartan:
                for i in l:
                    if i < 0:
                        self.cartanname += str(-i)
                    else:
                        self.cartanname += str(i)
        else:
            self.cartanname = ''
            for t in self.cartantype:
                self.cartanname += t[0]
                self.cartanname += str(len(t[1]))
                for i in t[1]:
                    self.cartanname += 'c'
                    self.cartanname += str(i)
        self.coxetermat = idmat(self.rank, 1)
        for s in self.rank:
            for t in range(s):
                if self.cartan[s][t] == 0:
                    self.coxetermat[s][t], self.coxetermat[t][s] = 2, 2
                elif self.cartan[s][t] * self.cartan[t][s] == 1:
                    self.coxetermat[s][t], self.coxetermat[t][s] = 3, 3
                elif self.cartan[s][t] * self.cartan[t][s] == 2:
                    self.coxetermat[s][t], self.coxetermat[t][s] = 4, 4
                elif self.cartan[s][t] * self.cartan[t][s] == 3:
                    self.coxetermat[s][t], self.coxetermat[t][s] = 6, 6
                elif self.cartan[s][t] * self.cartan[t][s] == 1 - self.cartan[s][t]:
                    self.coxetermat[s][t], self.coxetermat[t][s] = 5, 5
                else:
                    ty = typecartanmat([[self.cartan[s][s], self.cartan[t][s]],
                                        [self.cartan[s][t], self.cartan[t][t]]])
                    if ty[0][0] == 'I':
                        m = int(ty[0][1:])
                        self.coxetermat[s][t], self.coxetermat[t][s] = m, m
                    else:
                        self.coxetermat[s][t], self.coxetermat[t][s] = 'U', 'U'
        if split:
            self.split = self.rank
        else:
            self.split = split
            for s in self.rank:
                for t in range(s):
                    if self.coxetermat[s][t] != self.coxetermat[split[s]][split[t]]:
                        print("#W invalid permutation of generators !")
                        self.split = False
        self.fusions = {self.cartanname: {'subJ': self.rank, 'parabolic': True}}
        if fusion != []:
            self.fusions[fusion[0]] = {}
            for k in fusion[1]:
                self.fusions[fusion[0]][k] = fusion[1][k]
        self.matgens = []
        for s in self.rank:
            m = idmat(self.rank, 1)
            for t in self.rank:
                m[t][s] -= self.cartan[s][t]
            self.matgens.append(tuple([tuple(t) for t in m]))
        if isinstance(weightL, int):
            self.weightfunctions = [len(self.rank) * [weightL]]
        else:
            self.weightfunctions = [weightL[:]]
        self.param = param
        if self.cartantype[0][0] != 'U':
            self.roots, self.rootrepelms, self.rootorbits = roots(self.cartan)
            self.N = len(self.roots) // 2
            for o in self.rootorbits:
                o.sort()
            self.rootorbits1 = self.N * [0]
            for o in range(len(self.rootorbits)):
                for i in self.rootorbits[o]:
                    self.rootorbits1[i] = self.rootorbits[o][0]
            self.coxgens = [tuple([self.roots.index(tuple(t)) for t in m])
                            for m in self.matgens]
            self.permgens = permroots(self.cartan, self.roots)
            self.degrees = []
            for c in self.cartantype:
                self.degrees.extend(degreesdata(c[0], len(c[1])))
            self.degrees.sort()
            self.order = 1
            for d in self.degrees:
                self.order *= d
            b = []
            for c in self.cartantype:
                bl = len(c[1]) * [2]
                if c[0] == 'B':
                    bl[0] = 1
                if c[0] == 'C':
                    for i in range(1, len(c[1])):
                        bl[i] = 1
                if c[0] == 'F':
                    bl[2] = 1
                    bl[3] = 1
                if c[0] == 'G':
                    bl[0] = 3
                    bl[1] = 1
                if c[0][0] == 'I' and int(c[0][1:]) % 2 == 0:
                    bl[0] = -cartanmat(c[0], len(c[1]))[1][0]
                    bl[1] = 1
                b.extend(bl)
            p = []
            for c in self.cartantype:
                p.extend(c[1])
            self.symform = [b[p.index(i)] for i in self.rank]
            t1 = [[self.symform[i] * self.cartan[i][j] for j in self.rank]  # testing
                  for i in self.rank]
            for i in self.rank:
                for j in self.rank:
                    if i != j and t1[i][j] != t1[j][i]:
                        print("mist !")
                        return "mist"

    def __repr__(self):
        ct = self.cartantype
        if (len(ct) == 1 and ct[0][0] != 'U' and list(ct[0][1]) ==
                list(range(len(ct[0][1])))):
            return "coxeter('" + ct[0][0] + "'," + str(len(ct[0][1])) + ')'
        return 'coxeter(' + str(self.cartan) + ')'

    def coxelmlength(self, elm):
        """returns the length of a coxelm.
        """
        l = 0
        idm = self.roots[:len(self.rank)]
        m = [self.roots[i] for i in elm]
        while m != idm:
            s = 0
            while all(m[s][t] >= 0 for t in self.rank):
                s += 1
            m = [tuple([m[t][u] - self.cartan[s][t] * m[s][u]
                        for u in self.rank]) for t in self.rank]
            l += 1
        return l

    def matlength(self, mat):
        """returns the length of an element given as a matrix.
        """
        l = 0
        idm = self.roots[:len(self.rank)]
        m = list(mat)
        while m != idm:
            s = 0
            while all(m[s][t] >= 0 for t in self.rank):
                s += 1
            m = [tuple([m[t][u] - self.cartan[s][t] * m[s][u]
                        for u in self.rank]) for t in self.rank]
            l += 1
        return l

    def permlength(self, p):
        """returns the length of an element given as a full permutation.
        (Only works for finite W.)
        """
        return len([1 for i in p[:self.N] if i >= self.N])

    def coxelmtomat(self, elm):      # works for perms and coxelms
        """converts  elm (assumed to be a coxelm)  into  a matrix  with
        respect to the  simple reflections.   This also works if elm
        is a full permutation on the roots.
        """
        return tuple([self.roots[r] for r in elm[:len(self.rank)]])

    def coxelmtoperm(self, elm):      # works for perms and coxelms
        """converts a coxelm to a full permutation on the set of roots.
        (Only works for finite W.)
        """
        return tuple([self.roots.index(tuple([sum([r[i] * self.roots[elm[i]][s]
                                                   for i in self.rank]) for s in self.rank])) for r in self.roots])

    def coxelmtoword(self, elm):       # works for perms and coxelms
        """converts a  coxelm into a  reduced expression  in the simple
        reflections.
        """
        m = [self.roots[r] for r in elm[:len(self.rank)]]
        word = []
        weiter = True
        while weiter:
            s = 0
            while s < len(self.rank) and all(m[s][t] >= 0 for t in self.rank):
                s += 1
            if s < len(self.rank):
                m = [[m[t][u] - self.cartan[s][t] * m[s][u]
                      for u in self.rank] for t in self.rank]
                word.append(s)
            else:
                weiter = False
        return word

    def mattocoxelm(self, mat):
        """converts a matrix to a coxelm.
        """
        return tuple([self.roots.index(l) for l in mat])

    def mattoperm(self, mat):
        """converts a matrix to a full permutation on the set of roots.
        (Only works for finite W.)
        """
        return tuple([self.roots.index(tuple([sum([r[i] * mat[i][s]
                                                   for i in self.rank])
                                              for s in self.rank]))
                      for r in self.roots])

    def mattoword(self, mat):
        """converts  a  matrix to a  reduced expression  in the  simple
        reflections. This works for arbitrary Coxeter groups.
        """
        m = [list(l) for l in mat]
        word = []
        weiter = True
        while weiter:
            s = 0
            while s < len(self.rank) and all(m[s][t] >= 0 for t in self.rank):
                s += 1
            if s < len(self.rank):
                m = [[m[t][u] - self.cartan[s][t] * m[s][u] for u in self.rank]
                     for t in self.rank]
                word.append(s)
            else:
                weiter = False
        return word

    def permtoword(self, pw):
        """converts an element (given as a full permutation on the roots)
        into a reduced expression. (Only works for finite W.)
        """
        word = []
        p = pw[:]
        weiter = True
        while weiter:
            s = 0
            while s < len(self.rank) and p[s] < self.N:
                s += 1
            if s < len(self.rank):
                p = [p[i] for i in self.permgens[s]]
                word.append(s)
            else:
                weiter = False
        return word

    def wordtocoxelm(self, w):
        """converts any word in the simple reflections into a coxelm.
        (Only works for finite W.)
        """
        c = list(self.rank)
        for s in w:
            c = [self.permgens[s][c[i]] for i in self.rank]
        return tuple(c)

    def wordtomat(self, w):
        """converts  any word in the  simple reflections  into a matrix
        with respect to the basis of simple roots.  This  works  for
        arbitrary Coxeter groups.
        """
        m = idmat(self.rank, 1)
        for s in w[::-1]:
            m = [[m[t][u] - self.cartan[s][t] * m[s][u] for u in self.rank]
                 for t in self.rank]
        return tuple([tuple(l) for l in m])

    def wordtoperm(self, w):
        """converts  any word  in  the  simple reflections  into a full
        permutation on the set of roots. (Only works for finite W.)
        """
        l = [list(range(2 * self.N))]
        if not w:
            return tuple(l[0])
        l.extend([self.permgens[s] for s in w])
        return reduce(permmult, tuple(l))

    def stringtoword(self, sw):
        """converts a string (as returned, for example, by the function
        'allwordstrings' into a list.
        """
        if not sw:
            return []
        return [int(i) for i in sw.split('.')]

    def reducedword(self, w, W1):
        """converts  any word  in the simple reflections into a reduced
        expression in the  simple reflections.  If there is a fusion
        map into the Coxeter group W1, then the result is  expressed
        in the simple reflections of W1. In particular, this applies
        to the case where W1=W; in this case, the function turns the
        given word  w in W  into a (canonical) reduced expression in
        the simple reflections of W. This works for arbitrary W=W1.
        """
        f = self.fusions[W1.cartanname]['subJ']
        # if all(s in W1.rank for s in f):
        if self.fusions[W1.cartanname]['parabolic']:
            nw = [f[s] for s in w]
        else:
            nw = []
            for s in w:
                nw.extend(W1.rootrepelms[f[s]])
                nw.append(W1.rootorbits1[f[s]])
                nw.extend(W1.rootrepelms[f[s]][::-1])
        m = idmat(W1.rank, 1)
        for s in nw[::-1]:
            m = [[m[t][u] - W1.cartan[s][t] * m[s][u] for u in W1.rank]
                 for t in W1.rank]
        word = []
        weiter = True
        while weiter:
            s = 0
            while s < len(W1.rank) and all(m[s][t] >= 0 for t in W1.rank):
                s += 1
            if s < len(W1.rank):
                m = [[m[t][u] - W1.cartan[s][t] * m[s][u] for u in W1.rank]
                     for t in W1.rank]
                word.append(s)
            else:
                weiter = False
        return word

    def cycletyperoots(self, pw):
        """returns the cycle type of an element in its action  on  each
        of the root orbits. Here, the element is assumed to be given
        as a full permutation on all the roots.
        """
        ct = []
        for r in self.rootorbits:
            cl = []
            rest = r + [i + self.N for i in r]
            while rest:
                c = [rest[0]]
                for i in c:
                    if not pw[i] in c:
                        c.append(pw[i])
                cl.append(len(c))
                for i in c:
                    rest.remove(i)
                cl.sort()
            ct.append(tuple(cl))
        return tuple(ct)

    def permorder(self, pw):
        """returns the order of an element, given as a full  permutation
        on all roots. (Only works for finite W.)

        >>> W = coxeter('D',4)
        >>> w = W.wordtoperm([0,1])
        >>> W.permorder(w)
        2
        """
        if not pw:
            return 1
        return intlcmlist([y for x in self.cycletyperoots(pw) for y in x])

    def leftdescentsetperm(self, pw):
        """returns the left descent set of an element, given as a coxelm
        or a full permutation on all roots.
        """
        return [s for s in self.rank if pw[s] >= self.N]

    def rightdescentsetperm(self, pw):
        """returns the right descent set of an element, given as a full
        permutation on all roots.
        """
        ip = perminverse(pw)
        return [s for s in self.rank if ip[s] >= self.N]

    def leftdescentsetmat(self, mw):
        """returns the left descent set of an element, given as a matrix
        with respect to the basis of simple roots.
        """
        return [s for s in self.rank if all(mw[s][t] <= 0 for t in self.rank)]

    def rightdescentsetmat(self, mw):
        """returns the right descent set of an element, given as a matrix
        with respect to the basis of simple roots.
        """
        m = self.wordtomat(self.mattoword(mw)[::-1])
        return [s for s in self.rank if all(m[s][t] <= 0 for t in self.rank)]


def rmultgenmat(W, s, m):
    """returns the result of multiplying an element of W on the right
    by a simple reflection. The element is assumed to  be given as
    a matrix.

    >>> W = coxeter("B",3)
    >>> m = rmultgenmat(W,2,W.wordtomat([0,1])); m
    [[-1, -1, -1], [2, 1, 1], [0, 1, 0]]
    >>> W.mattoword(m)
    [0, 1, 2]

    See also 'lmultmatgen' and 'conjgenmat'.
    """
    nw = [list(m[x]) for x in W.rank]
    Wcartan_s = W.cartan[s]
    for t in W.rank:
        nwt = nw[t]
        nw[t][s] -= sum(nwt[u] * Wcartan_s[u] for u in W.rank
                        if Wcartan_s[u])
    return nw

# F lmultgenmat  # is slightly faster than rmultgen


def lmultgenmat(W, s, m):
    """returns the result of multiplying an element of W on the left
    by a simple reflection. The element is assumed to be given as
    a matrix.

    See also 'rmultgenmat'.
    """
    return tuple([tuple([m[t][u] - W.cartan[s][t] * m[s][u] for u in W.rank])
                  for t in W.rank])


def conjgenmat(W, s, m):
    """conjugates an element (given as a matrix) by a generator.

    See also 'rmultgenmat'.
    """
    nw = [[m[t][u] - W.cartan[s][t] * m[s][u] for u in W.rank] for t in W.rank]
    for t in W.rank:
        nw[t][s] -= sum(nw[t][u] * W.cartan[s][u] for u in W.rank
                        if W.cartan[s][u] != 0)
    return tuple([tuple(l) for l in nw])


def conjgencoxelm(W, s, w):
    """conjugates an element (given as a coxelm) by a generator.
    """
    return tuple([W.permgens[s][r] for r in
                  [W.roots.index(tuple([W.roots[w[t]][u] -
                                        W.cartan[s][t] * W.roots[w[s]][u]
                                        for u in W.rank])) for t in W.rank]])


def conjgenperm(W, s, pw):
    """conjugates an element (given as a full permutation on the set of
    roots by a generator.
    """
    return tuple([W.permgens[s][pw[W.permgens[s][r]]] for r in range(2 * W.N)])


def conjugacyclass(W, pw, verbose=False):
    """returns the set of all elements in a conjugacy class,  ordered by
    increasing length.  The argument is supposed  to be a  permutation
    and the elements in the resulting list are permutations. Elements
    of minimum length are more efficiently computed using 'classmin'.

    >>> W = coxeter("F",4)
    >>> [W.permtoword(w) for w in conjugacyclass(W,W.permgens[1])]
    [[1],
     [0],
     [0, 1, 0],
     [2, 1, 2],
     [0, 2, 1, 0, 2],
     [3, 2, 1, 2, 3],
     [1, 0, 2, 1, 0, 2, 1],
     [0, 3, 2, 1, 0, 2, 3],
     [1, 0, 3, 2, 1, 0, 2, 1, 3],
     [2, 1, 0, 3, 2, 1, 0, 2, 1, 3, 2],
     [1, 2, 1, 0, 3, 2, 1, 0, 2, 1, 3, 2, 1],
     [0, 1, 2, 1, 0, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0]]

    See also 'conjugacyclasses', 'classmin' and 'involutions'.
    """
    cl = [pw]
    cl1 = set([bytes(pw[:len(W.rank)])])
    for x in cl:
        for s in W.permgens:
            sxs = tuple([s[x[s[r]]] for r in range(2 * W.N)])
            bsxs = bytes(sxs[:len(W.rank)])
            if bsxs not in cl1:
                cl.append(sxs)
                cl1.add(bsxs)
    if verbose:
        print(f'🄸 Size of class: {len(cl)}\n')
    laux = sorted(((w, W.permlength(w)) for w in cl), key=lambda wl: wl[1])
    return [w for w, l in laux]


def involutions(W):
    """returns the list of involutions in a finite Coxeter group
    (as full permutations on the roots).

    sage: W = coxeter("A",2)
    sage: involutions(W)
    [(0, 1, 2, 3, 4, 5),
    (3, 2, 1, 0, 5, 4),
    (2, 4, 0, 5, 1, 3),
    (4, 3, 5, 1, 0, 2)]
    """
    t = tuple(W.rank)
    return flatlist([conjugacyclass(W, W.wordtoperm(w))
                     for w in conjugacyclasses(W)['reps']
                     if W.wordtocoxelm(2 * w) == t])


def cyclicshiftorbit(W, pw):
    """returns the orbit of an element under cyclic shift.

    sage: W = coxeter("A",2)
    sage: w = W.wordtoperm([0,1])
    sage: cyclicshiftorbit(W, w)
    [(5, 0, 4, 2, 3, 1), (1, 5, 3, 4, 2, 0)]

    See also 'testcyclicshift'.
    """
    bahn = [pw[:]]
    l = len([1 for i in pw[:W.N] if i >= W.N])
    for b in bahn:
        for s in W.rank:
            nw = tuple([W.permgens[s][b[W.permgens[s][r]]]
                        for r in range(2 * W.N)])
            if len([1 for i in nw[:W.N] if i >= W.N]) == l and nw not in bahn:
                bahn.append(nw)
    return bahn


def testcyclicshift(W, pw):
    """tests if an element (given  as a full permutation on the roots)
    has minimal length in its conjugacy class; if this is the case,
    True is returned. Otherwise, the function returns a pair  (x,s)
    where  x is an element and s  is a  simple reflection such that
    l(x)<l(sxs) and sxs lies in the same cyclic chift class as pw.

    >>> W = coxeter("F",4)
    >>> t = testcyclicshift(W,W.wordtoperm([0,1,2,1,0])); print(t)
    [(13, 32, 2, 9, 4, 29, 12, 7, 25, 3, 10, 16, 6, 0, 18, 15, 11, 22, 14, 19, 20, 21, 17,
     23, 37, 8, 26, 33, 28, 5, 36, 31, 1, 27, 34, 40, 30, 24, 42, 39, 35, 46, 38, 43, 44,
     45, 41, 47), 0]
    >>> W.permtoword(t[0])
    [1, 2, 1]

    See also 'classpolynomials'.
    """
    bahn = [pw[:]]
    l = len([1 for i in pw[:W.N] if i >= W.N])
    for b in bahn:
        for s in W.rank:
            nw = tuple([W.permgens[s][b[W.permgens[s][r]]]
                        for r in range(2 * W.N)])
            lnw = len([1 for i in nw[:W.N] if i >= W.N])
            if lnw < l:
                return [nw, s]
            elif lnw == l and nw not in bahn:
                bahn.append(nw)
    return True


def conjtomin(W, pw):
    """returns an element  of minimal length (as a reduced word) in
    the conjugacy class of pw.

    >>> W = coxeter("E",6); w0=longestperm(W); W.permlength(w0)
    36
    >>> conjtomin(W,w0)
    [1, 2, 3, 1, 2, 3, 4, 3, 1, 2, 3, 4]

    See also 'cyclicshiftclass', 'testcyclicshift' and 'conjugacyclasses'.
    """
    alt = pw[:]
    neu = testcyclicshift(W, alt)
    while neu is not True:
        alt = neu[0][:]
        neu = testcyclicshift(W, alt)
    return W.permtoword(alt)


def classmin(W, w, minl=True, verbose=False):
    """returns the elements of minimal length in a conjugacy class
    of a given element.

    >>> W = coxeter("E",8)
    >>> [W.permtoword(x) for x in classmin(W,[0])]
    [[0], [2], [3], [1], [4], [5], [6], [7]]

    It is assumed that the given element has  minimal length in
    its class. Otherwise,  the extra argument  'minl' has to be
    set to some value unequal to 'True'.

    >>> [W.permtoword(x) for x in classmin(W,[0,2,0],minl=0)]
    [[2], [0], [3], [1], [4], [5], [6], [7]]

    See also 'conjugacyclass', 'cyclicshiftclass' and 'conjtomin'.
    """
    if verbose:
        print('🄸 ')
    if minl:
        l = len(w)
        J0 = set(w)
        cl = [W.wordtoperm(w)]
    else:
        alt = W.wordtoperm(w)
        neu = testcyclicshift(W, alt)
        while neu is not True:
            alt = neu[0][:]
            neu = testcyclicshift(W, alt)
        cl = [alt]
        w1 = W.permtoword(alt)
        l = len(w1)
        J0 = set(w1)
    cl1 = set([bytes(cl[0][:len(W.rank)])])
    subs = {}
    for cc in coxeterclasses(W):
        Jb = [i for i in range(len(cc)) if cc[i] == '1']
        if len(Jb) == len(J0) + 1:
            subs[tuple(Jb)] = longestperm(W, Jb)
    if verbose:
        print('+')
    for x in cl:
        Jx = list(set(W.permtoword(x)))
        for s in W.rank:
            if s not in Jx:
                J = Jx + [s]
                J.sort()
                w0 = subs[tuple(J)]
                x1 = tuple([w0[x[w0[r]]] for r in range(2 * W.N)])
                bx1 = bytes(x1[:len(W.rank)])
                if bx1 not in cl1:
                    cl.append(x1)
                    cl1.add(bx1)
    if verbose:
        print('+ ')
    for b in cl:
        for s in W.rank:
            nw = tuple([W.permgens[s][b[W.permgens[s][r]]]
                        for r in range(2 * W.N)])
            nw1 = bytes(nw[:len(W.rank)])
            if W.permlength(nw) == l and nw1 not in cl1:
                cl.append(nw)
                cl1.add(nw1)
    if verbose:
        print('Size of Cmin: ' + str(len(cl)) + '\n')
    # test
    # cm=[x for x in conjugacyclass(W,cl[0]) if W.permlength(x)==l]
    # if len(cm)!=len(cl) or any(not bytes(x[:len(W.rank)]) in cl1 for x in cm):
    #  return False
    return cl


def longestperm(W, J=0):
    """returns  the unique element of maximal length in W  (where W is
    assumed to be finite) as a permutation of the set of all roots.
    If the additional argument J is specified, the function returns
    the longest element in the parabolic subgroup generated by J.

    >>> W = coxeter("F",4)
    >>> w0 = longestperm(W); print(w0)
    (24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
     45, 46, 47, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
     20, 21, 22, 23)
    >>> W.permtoword(w0)                   # reduced expression
    [0, 1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]
    >>> [W.roots[i] for i in w0[:4]]           # as a matrix
    [(-1, 0, 0, 0), (0, -1, 0, 0), (0, 0, -1, 0), (0, 0, 0, -1)]
    >>> W.permtoword(longestperm(W,[1,2])) # parabolic of type C_2
    [1, 2, 1, 2]
    """
    if J == 0:
        J = W.rank
    if J == W.rank:
        try:
            return W.longestperm
        except AttributeError:
            pass

    p = list(range(2 * W.N))
    while any(p[t] < W.N for t in J):
        s = 0
        while p[J[s]] >= W.N:
            s += 1
        p = [p[i] for i in W.permgens[J[s]]]
    if J == list(W.rank):
        W.longestperm = tuple(p)
        return W.longestperm
    return tuple(p)


def bruhatmat(W, y, w):
    """returns true or false according to whether y is less than or equal
    to w in the Bruhat-Chevalley order on W. Here, y and w are assumed
    to be matrices. (This function also works for infinite W.)

    The algorithm is based on the following recursion. Let w in W.  If
    w is not the identity, let s be  any  simple reflection such  that
    l(sw)=l(w)-1. Then y <= w if and only if sy<=sw  (if l(sy)=l(y)-1)
    or y<=sw  (if l(sy)=l(y)+1).

    See also 'bruhatperm' and 'bruhat'.
    """
    id = tuple([tuple(l) for l in idmat(W.rank, 1)])
    if y == id or y == w:
        return True
    elif w == id:
        return y == w
    else:
        s = 0
        while s < len(W.rank) and all(w[s][t] >= 0 for t in W.rank):
            s += 1
        if s == len(W.rank):
            print([y, w, s])
        nw = lmultgenmat(W, s, w)
        if any(y[s][t] < 0 for t in W.rank):
            ny = lmultgenmat(W, s, y)
            return bruhatmat(W, ny, nw)
        else:
            return bruhatmat(W, y, nw)


def bruhatcoxelm(W, y, w) -> bool:
    """returns true or false according to whether y is less than or equal
    to w in the Bruhat-Chevalley order on W. Here, y and w are assumed
    to be coxelms.

    The algorithm is based on the following recursion. Let w in W.  If
    w is not the identity, let s be  any  simple reflection such  that
    l(sw)=l(w)-1. Then y <= w if and only if sy<=sw  (if l(sy)=l(y)-1)
    or y<=sw  (if l(sy)=l(y)+1).

    >>> W = coxeter("H", 3);
    >>> w = W.wordtocoxelm([0, 1, 0, 2])
    >>> b = [y for y in redleftcosetreps(W) if bruhatcoxelm(W,y,w)]

    all y in W such that y<=w:

    >>> [W.coxelmtoword(y) for y in b]
    [[],
     [1],
     [0],
     [2],
     [1, 2],
     [0, 1],
     [0, 2],
     [1, 0],
     [0, 1, 2],
     [1, 0, 2],
     [0, 1, 0],
     [0, 1, 0, 2]]

    See also 'bruhatperm' and 'bruhatmat'.
    """
    if y == tuple(W.rank) or y == w:
        return True
    if w == tuple(W.rank):
        return y == w
    s = 0
    while w[s] < W.N:
        s += 1
    nw = tuple([W.roots.index(tuple([W.roots[w[t]][u] - W.cartan[s][t] *
                                     W.roots[w[s]][u] for u in W.rank])) for t in W.rank])
    if y[s] >= W.N:
        ny = tuple([W.roots.index(tuple([W.roots[y[t]][u] - W.cartan[s][t] *
                                         W.roots[y[s]][u] for u in W.rank])) for t in W.rank])
        return bruhatcoxelm(W, ny, nw)
    else:
        return bruhatcoxelm(W, y, nw)


def bruhatperm(W, x, y, lx=False, ly=False) -> bool:
    """returns true or false according to whether y is less than or equal
    to w in the Bruhat-Chevalley order on W. Here, y and w are assumed
    to be  full permutations on the roots.  The lengths of  y,w can be
    passed as optional arguments.

    The algorithm is based on the following recursion. Let w in W.  If
    w is not the identity, let s be  any  simple reflection such  that
    l(sw)=l(w)-1. Then y <= w if and only if sy<=sw  (if l(sy)=l(y)-1)
    or y<=sw  (if l(sy)=l(y)+1).

    See also 'bruhat' and 'bruhatcoxelm'.
    """
    if x == tuple(range(2 * W.N)) or x == y:
        return True
    if y == tuple(range(2 * W.N)):
        return x == y

    if lx is False:
        lx = W.permlength(x)
    if ly is False:
        ly = W.permlength(y)
    while lx < ly and lx != 0 and ly != 0:
        s = 0
        while y[s] < W.N:
            s += 1
        if x[s] >= W.N:
            x = tuple([x[r] for r in W.permgens[s]])
            lx -= 1
        y = tuple([y[r] for r in W.permgens[s]])
        ly -= 1
    return lx == 0 or (lx == ly and x == y)


def bruhat(W, y, w) -> bool:
    """returns true or false according to whether y is less than or equal
    to w in the Bruhat-Chevally order on W. This is a generic function
    which checks the type of  y and  w  and then calls one of the more
    specialised functions, 'bruhatcoxelm', 'bruhatmat', 'bruhatperm'.

    The function is based on the following recursion.  Let w in W.  If
    w is not the identity, let s be  any  simple reflection  such that
    l(sw)=l(w)-1.  Then y <= w if and only if sy<=sw (if l(sy)=l(y)-1)
    or y<=sw  (if l(sy)=l(y)+1).

    >>> W = coxeter("H",3)
    >>> w = W.wordtocoxelm([0,1,0,2])
    >>> b = (y for y in redleftcosetreps(W) if bruhat(W,y,w))
    >>> [W.coxelmtoword(y) for y in b]
    [[],
     [1],
     [0],
     [2],
     [1, 2],
     [0, 1],
     [0, 2],
     [1, 0],
     [0, 1, 2],
     [1, 0, 2],
     [0, 1, 0],
     [0, 1, 0, 2]]

    These are all y in W such that y<=w.

    If y,w are known to be coxelms, then it is more efficient to  call
    directly 'bruhatcoxelm(W,y,w)'.  Similarly  for matrices  and full
    permutations.
    """
    if len(y) == len(W.rank) and isinstance(y[0], int):  # coxelms
        return bruhatcoxelm(W, y, w)
    if len(y) == 2 * W.N:                                # full permutations
        return bruhatperm(W, y, w)
    if isinstance(y[0], (tuple, list)):                  # matrices
        return bruhatmat(W, y, w)


def reflections(W):
    """returns the list of reflections of W (where W is assumed
    to be finite),  as permutations on the set of all roots.

    The  i-th element in  this list is the reflection  whose
    root is the i-th element of W.roots.

    >>> W = coxeter("I5",2)
    >>> r = reflections(W); r
    [(5, 2, 1, 4, 3, 0, 7, 6, 9, 8),
     (3, 6, 4, 0, 2, 8, 1, 9, 5, 7),
     (9, 3, 7, 1, 5, 4, 8, 2, 6, 0),
     (2, 9, 0, 8, 6, 7, 4, 5, 3, 1),
     (6, 5, 8, 7, 9, 1, 0, 3, 2, 4)]
    >>> [W.permtoword(p) for p in r]
    [[0], [1], [0, 1, 0], [1, 0, 1], [0, 1, 0, 1, 0]]

    See also 'reflectionsubgroup'.
    """
    try:
        return W.reflections
    except AttributeError:
        pass
    refl = []
    for r in range(W.N):
        w = W.rootrepelms[r][:]
        w.append(W.rootorbits1[r])
        w.extend(W.rootrepelms[r][::-1])
        refl.append(w[:])
    W.reflections = [W.wordtoperm(r) for r in refl]
    return W.reflections


def innerprodroots(W, r1, r2):
    p = 0
    for u in W.rank:
        if W.roots[r1][u] != 0:
            for v in W.rank:
                if W.cartan[u][v] != 0 and W.roots[r2][v] != 0:
                    p += W.roots[r1][u] * W.symform[u] * \
                        W.cartan[u][v] * W.roots[r2][v]
    return p


def reflectionsubgroup(W, J):
    """returns the subgroup of  W generated by the reflections in the
    list J. The result is again a  Coxeter group in its own right;
    the embedding into W is specified  in the attribute 'fusions'.

    Any Coxeter group has such a  'fusions' attribute;  this  is a
    nested dictionary which contains at least one entry:  that  of
    the embedding of  W into itself.  (This  design  is  different
    from that in gap-chevie;  it  appears to be  better  suited to
    recursive algorithms involving various reflection  subgroups.)

    Let H be a Coxeter group  created as  above,  as a subgroup of
    some bigger group W. Then 'H.fusions' will have an entry

        { W.cartanname: { "subJ": list, ... }, ... }

    where  list gives the embedding of the simple reflections of H
    into the set of reflections of W. If J just consists of simple
    reflections of W, then H  is a parabolic subgroup and the list
    equals  J;  otherwise, list[i] is the index of the i-th simple
    reflection of the  subgroup in the  list of  reflections of W.
    (Further entries of 'H.fusions' may contain information on the
    fusion of conjugacy classes and so on.)

    See also 'reflections'.

    >>> W = coxeter("F",4)
    >>> W.cartantype
    [['F', [0, 1, 2, 3]]]
    >>> W.cartanname
    'F4c0c1c2c3'
    >>> W.fusions              # W only has the fusion into itself
    {'F4c0c1c2c3': {'parabolic': True, 'subJ': [0, 1, 2, 3]}}

    >>> H = reflectionsubgroup(W,[1,2,3,23])
    >>> H.cartantype
    [['C', [0, 1, 2]], ['A', [3]]]
    >>> H.cartanname
    'C3c0c1c2A1c3'
    >>> H.fusions        # H has the fusion into itself and into W
    {'C3c0c1c2A1c3': {'parabolic': True, 'subJ': [0, 1, 2, 3]},
     'F4c0c1c2c3': {'parabolic': False, 'subJ': [1, 2, 3, 23]}}
    >>> w = longestperm(H); w[:4]
    (10, 11, 12, 13)
    >>> w1 = H.permtoword(w); w1    # reduced word inside H
    [0, 1, 0, 1, 2, 1, 0, 1, 2, 3]
    >>> H.reducedword(w1,W)   # and now in W, using the fusion map
    [0, 1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]

    >>> W = coxeter(affinecartanmat("G",2)); W.cartanname
    'U210121032'
    >>> H = reflectionsubgroup(W,[1,2]); H.cartanname
    'G2c0c1'
    >>> H.fusions
    {"G2c0c1":{'subJ':[0,1],     'parabolic':True},
      "U210121032":{'subJ':[1,2],'parabolic':False}}
    >>> H.reducedword([0,1],W)
    [1, 2]

    Remark: If J is a subset of the set of simple reflections of W
    then J will not be sorted internally.  So  this can be used to
    create a copy of W with the simple reflections relabelled.

    >>> W = coxeter("F",4);
    >>> H = reflectionsubgroup(W,[1,3,0,2])
    >>> H.cartantype
    [['F', [2, 0, 3, 1]]]
    >>> H.fusions
    {'F4c0c1c2c3': {'parabolic': True, 'subJ': [1, 3, 0, 2]},
     'F4c2c0c3c1': {'parabolic': True, 'subJ': [0, 1, 2, 3]}}
    >>> W.cartanname
    'F4c0c1c2c3'
    """
    para = True
    if not J:
        cartanJ = [[]]
        fundJ = []
    elif all(s in W.rank for s in J):
        fundJ = list(J[:])
    # fundJ.sort()
        cartanJ = [[W.cartan[s][t] for t in fundJ] for s in fundJ]
    # reflectionsJ=[]
    # for r in roots(cartanJ)[0]:
    #   if all(u>=0 for u in r):
    #     c=len(W.rank)*[0]
    #     for j in range(len(J)):
    #       c[fundJ[j]]=r[j]
    else:
        para = False
        refls = reflections(W)
        gen = []
        for j in J:
            if j >= W.N:
                gen.append(refls[j - W.N])
            else:
                gen.append(refls[j])
        orb = J[:]
        for o in orb:
            for g in gen:
                if not g[o] in orb:
                    orb.append(g[o])
        reflectionsJ = set(filter(lambda x: x < W.N, orb))
        fundJ = []
        for r in reflectionsJ:
            pw = refls[r]
            if len(set(filter(lambda x: pw[x] >= W.N, range(W.N))) & reflectionsJ) == 1:
                fundJ.append(r)
        fundJ.sort()
        if max(flatlist(W.coxetermat)) > 5:
            mat = [[innerprodroots(W, r1, r2) for r2 in fundJ] for r1 in fundJ]
            cartanJ = [[(2 * mat[i][j]) // mat[i][i] for j in range(len(mat))]
                       for i in range(len(mat))]
        else:
            cartanJ = [[(sum(W.roots[j]) - sum(W.roots[refls[i][j]])) // sum(W.roots[i])
                        for j in fundJ] for i in fundJ]
    return coxeter(cartanJ, fusion=[W.cartanname, {'subJ': fundJ[:],
                                                   'parabolic': para}])


def reducedunique(W, pw) -> bool:
    """checks if an element has a unique reduced expression.
    """
    if pw == tuple(range(2 * W.N)):
        return True
    l = W.leftdescentsetperm(pw)
    if len(l) > 1:
        return False
    return reducedunique(W, tuple(pw[i] for i in W.permgens[l[0]]))


def allmats(W, maxl=-1, verbose=False):
    """returns all elements of W of length at most maxl, represented
    as matrices.  Along the computation, the function  prints the
    number of elements of length i for i between 0 and max.  This
    function also works for infinite W. If the argument 'maxl' is
    omitted and W is finite,  all elements will be computed.

    >>> W = coxeter("A",2)
    >>> allmats(W)
    [[((1, 0), (0, 1))],
     [((-1, 0), (1, 1)), ((1, 1), (0, -1))],
     [((0, 1), (-1, -1)), ((-1, -1), (1, 0))],
     [((0, -1), (-1, 0))]]

    >>> W = coxeter(affinecartanmat("G",2));
    >>> W.cartantype
    [['U', [0, 1, 2]]]
    >>> print(W.cartan)
    [[2, -1, 0], [-1, 2, -1], [0, -3, 2]]
    >>> [[W.mattoword(m) for m in l] for l in allmats(W,3)]
    [[[]],
     [[2], [1], [0]],
     [[0, 1], [1, 2], [0, 2], [1, 0], [2, 1]],
     [[0, 1, 2], [1, 0, 2], [0, 1, 0], [2, 1, 2], [0, 2, 1], [2, 1, 0], [1, 2, 1]]]

    See also 'allcoxelms', 'allwords' and 'allelmsproperty'.
    """
    if 'N' in dir(W):
        if maxl == -1:
            maxlen = W.N
        else:
            maxlen = min(maxl, W.N)
    else:
        maxlen = maxl
    cryst = all(isinstance(x, int) for x in flatlist(W.cartan))
    l = [[tuple(tuple(l) for l in idmat(W.rank, 1))]]
    poin = [1]
    if verbose:
        print('🄸 1 ')
    for i in range(maxlen):
        nl = []
        for w in l[i]:
            for s in W.rank:
                if all(w[s][t] >= 0 for t in W.rank):
                    nl.append(tuple([tuple([w[t][u] - W.cartan[s][t] * w[s][u]
                                           for u in W.rank]) for t in W.rank]))
        if cryst:
            l.append(list(set(nl)))
        else:
            nl1 = []
            for x in nl:
                if x not in nl1:
                    nl1.append(x)
            l.append(nl1[:])
        poin.append(len(l[i + 1]))
        if verbose:
            print(str(len(l[i + 1])) + ' ')
    W.allmats = [l[i] for i in range(maxlen + 1)]
    if verbose:
        print('\n')
    return l


def allcoxelms(W, maxl=-1, verbose=False):
    """returns all elements of W of length at most maxl, represented
    as coxelms, that is, permutations of the set of all roots where
    only the images of the simple roots are given.  This only works
    for finite W. (If maxl is not specified, then all elements will
    be returned.)

    >>> W = coxeter("A",2)
    >>> a = allcoxelms(W); a
    [[(0, 1)], [(3, 2), (2, 4)], [(5, 0), (1, 5)], [(4, 3)]]
    >>> [[W.coxelmtoword(i) for i in l] for l in a]
    [[[]], [[0], [1]], [[0, 1], [1, 0]], [[0, 1, 0]]]

    (Use 'flatlist' to create one long list of the elements.)

    See also 'allmats, 'allelmchain' and 'allelmsproperty'.
    """
    if maxl == -1:
        maxlen = W.N
    else:
        maxlen = min(maxl, W.N)
    l = [[tuple(W.rank)]]
    poin = [1]
    ll = longestperm(W)
    if verbose:
        print('🄸 1 ')
    for i in range(maxlen):
        if i < W.N / 2:
            nl = []
            for w in l[i]:
                for s in W.rank:
                    if w[s] < W.N:
                        nl.append(tuple([W.roots.index(tuple([W.roots[w[t]][u] -
                                                              W.cartan[s][t] * W.roots[w[s]][u] for u in W.rank]))
                                         for t in W.rank]))
            l.append(list(set(nl)))
        else:
            l.append([tuple([ll[w[s]] for s in W.rank]) for w in l[W.N - i - 1]])
        poin.append(len(l[i + 1]))
        if verbose:
            print(str(len(l[i + 1])) + ' ')
    if verbose:
        print('\n')
    return l


def redleftcosetreps(W, J=[]):
    """returns the list of  distinguished  left  coset representatives
    of the  parabolic subgroup  H of W  which is  generated  by the
    simple reflections in J;  if no argument J is specified, then J
    is set to be [].  An element w in W belongs to this  set if and
    only if w has minimal length in the coset w*H or, equivalently,
    l(ws)=l(w)+1  for all s in J.  The  elements  are  returned  as
    coxelms, ordered by increasing length.

    >>> W = coxeter("A",4)
    >>> a = redleftcosetreps(W,[0,1,2])
    >>> a
    [(0, 1, 2, 3), (0, 1, 6, 13), (0, 8, 16, 2), (9, 18, 1, 2), (19, 0, 1, 2)]
    >>> [W.coxelmtoword(c) for c in a]
    [[], [3], [2, 3], [1, 2, 3], [0, 1, 2, 3]]

    See also 'redrightcosetreps' and 'redinrightcoset'.
    """
    l, ol = [tuple(W.rank)], [tuple(W.rank)]
    while ol:
        nl = []
        for w in ol:
            for s in W.rank:
                if w[s] < W.N:
                    nw = tuple([W.roots.index(tuple([W.roots[w[t]][u] -
                                                     W.cartan[s][t] * W.roots[w[s]][u]
                                                     for u in W.rank])) for t in W.rank])
                    if all(tuple([W.permgens[u][r] for r in w]) != nw for u in J):
                        nl.append(nw)
        ol = set(nl)
        if ol:
            l.extend(ol)
    return l


def redrightcosetreps(W, H):
    """returns the list of  distinguished right  coset representatives
    of the reflection subgroup H of W. An element w in W belongs to
    this  set if and only if w has minimal length in the coset  H*w
    or, equivalently, w sends each simple root  of  H to a positive
    root of W. The  elements are  returned  as  coxelms, ordered by
    increasing length.

    >>> W = coxeter("A",4)
    >>> H = reflectionsubgroup(W,[0,1,2])
    >>> a = redrightcosetreps(W, H); a
    [(0, 1, 2, 3), (0, 1, 6, 13), (0, 5, 3, 16), (4, 2, 3, 18), (1, 2, 3, 19)]
    >>> [W.coxelmtoword(c) for c in a]
    [[], [3], [3, 2], [3, 2, 1], [3, 2, 1, 0]]

    >>> W = coxeter("F",4);
    >>> H = reflectionsubgroup(W,[3,1,2,W.N-1]);H.cartantype   # non-parabolic
    [['C', [0, 1, 2]], ['A', [3]]]
    >>> [W.coxelmtoword(p) for p in redrightcosetreps(W,H)]
    [[],
     [0],
     [0, 1],
     [0, 1, 2],
     [0, 1, 2, 1],
     [0, 1, 2, 3],
     [0, 1, 2, 1, 0],
     [0, 1, 2, 1, 3],
     [0, 1, 2, 1, 0, 3],
     [0, 1, 2, 1, 3, 2],
     [0, 1, 2, 1, 0, 3, 2],
     [0, 1, 2, 1, 3, 2, 1]]

    See also 'redinrightcoset' and 'redleftcosetreps'.
    """
    if H.fusions[W.cartanname]['parabolic']:
        l, ol = [tuple(W.rank)], [tuple(W.rank)]
    else:
        l, ol = [tuple(range(2 * W.N))], [tuple(range(2 * W.N))]
    ol1 = []
    J = H.fusions[W.cartanname]['subJ']
    while ol:
        nl = []
        for w in ol:
            for s in W.rank:
                nw = tuple([W.permgens[s][i] for i in w])
                if nw not in ol1:
                    if all(nw[u] < W.N for u in J):
                        nl.append(nw)
        ol1 = list(ol)
        ol = set(nl)
        if ol:
            l.extend(list(ol))
    return [p[:len(W.rank)] for p in l]


def redinrightcoset(W, H, w):
    """returns the unique reduced element in the coset H*w; this is
    defined by the condition that it sends all simple roots of H
    to positive roots in W. Here, w can be either a coxelm  or a
    full permutation on the roots, and the output will be of the
    same type.

    >>> W = coxeter("F",4)
    >>> H = reflectionsubgroup(W,[0,1,8,15]); H.cartantype     # non-parabolic
    [['D', [1, 3, 0, 2]]]
    >>> W.coxelmtoword(redinrightcoset(W,H,W.wordtocoxelm([2,1,2,3,2,1])))
    [3, 2]

    See also 'redrightcosetreps'.
    """
    J = H.fusions[W.cartanname]['subJ']
    refls = reflections(W)
    if len(w) == len(W.rank):
        nw = W.coxelmtoperm(w)
        l = len(W.rank)
    else:
        nw = w[:]
        l = 2 * W.N
    while any(nw[u] >= W.N for u in J):
        s = 0
        while nw[J[s]] < W.N:
            s += 1
        nw = [nw[i] for i in refls[J[s]]]
    return tuple(nw[:l])


def allelmchain(W, depth=1):
    """returns a  sequence  (corresponding to a chain of parabolic subgroups)
    of lists of  distinguished right coset representatives where,  at each
    step  in the chain, the  rank decreases by  1 and the  chain decreases
    until the rank equals the  optional argument  depth.  (More precisely,
    we remove the last simple reflection at each step.)  This can  be used
    to run through all elements of W  (where  W is  finite)  without first
    constructing a complete list; see also 'allelmsproperty'.  The various
    coset representatives are all expressed as reduced words in the simple
    reflections of W. This works efficiently even for groups of relatively
    large rank (including all the groups of exceptional type).

    >>> W = coxeter("A",5)
    >>> a = allelmchain(W,depth=3); a
    [[[],
      [2],
      [1],
      [0],
      [1, 2],
      [0, 2],
      [1, 0],
      [0, 1],
      [2, 1],
      [0, 2, 1],
      [1, 0, 2],
      [0, 1, 2],
      [1, 2, 1],
      [2, 1, 0],
      [0, 1, 0],
      [0, 2, 1, 0],
      [0, 1, 0, 2],
      [1, 2, 1, 0],
      [1, 0, 2, 1],
      [0, 1, 2, 1],
      [0, 1, 0, 2, 1],
      [0, 1, 2, 1, 0],
      [1, 0, 2, 1, 0],
      [0, 1, 0, 2, 1, 0]],
     [[], [3], [3, 2], [3, 2, 1], [3, 2, 1, 0]],
     [[], [4], [4, 3], [4, 3, 2], [4, 3, 2, 1], [4, 3, 2, 1, 0]]]

    Here, the 24 elements of a[0] are all the elements of the  parabolic
    subgroup generated by 0,1,2 (type A_3); then a[1] contains the right
    coset representatives of the  latter subgroup  inside the  parabolic
    subgroup generated by 0,1,2,3 (type A_4); finally, a[2] contains the
    right coset  representatives of the latter subgroup inside the whole
    group. Thus,

            { x + y + z | x in a[0], y in a[1], z in a[2] }

    contains each element of W exactly once (where,  as usual in python,
    the '+' denotes concatenation of words).  Furthermore,  each reduced
    expression w=x+y+z obtained as above is equal to W.reducedword(w,W).

    See also 'redrightcosetreps' and 'allelmsproperty'.
    """
    if len(W.rank) <= depth:
        el = [[W.coxelmtoword(c) for c in redrightcosetreps(W,
                                                            reflectionsubgroup(W, []))]]
    else:
        el = [[W.coxelmtoword(c) for c in redrightcosetreps(W,
                                                            reflectionsubgroup(W, list(W.rank)[:-1]))]]
        for k in range(len(W.rank) - depth - 1):
            J = list(W.rank)[:-k - 1]
            W1 = coxeter([[W.cartan[i][j] for j in J] for i in J])
            el.append([W1.coxelmtoword(c) for c in redrightcosetreps(W1,
                                                                     reflectionsubgroup(W1, J[:-1]))])
        W2 = coxeter([[W.cartan[i][j] for j in range(depth)]
                      for i in range(depth)])
        el.append([W2.coxelmtoword(c) for c in redrightcosetreps(W2,
                                                                 reflectionsubgroup(W2, []))])
    size = 1
    for l in el:
        size *= len(l)
    if size != W.order:
        print("mist !")
        return "mist"
    return el[::-1]


def allelmchain1(W):
    """returns a sequence  (corresponding to a chain of parabolic subgroups)
    of lists of  distinguished left  coset representatives where, at each
    step  in the chain, the  rank decreases by  1 and the chain decreases
    until rank 3 is reached. (More precisely, we successfully remove  the
    last simple reflection at each step.) This can be used to run through
    all elements of W (where W is finite) without constructing a complete
    list. The  various left  coset representatives  are all  expressed as
    reduced words in the simple reflections of W. This  works efficiently
    even for groups of relatively large rank, e.g., type E_8.

    >>> W = coxeter("A",5)
    >>> a = allelmchain1(W); a
    [[[], [4], [3, 4], [2, 3, 4], [1, 2, 3, 4], [0, 1, 2, 3, 4]],
     [[], [3], [2, 3], [1, 2, 3], [0, 1, 2, 3]],
     [[],
      [2],
      [1],
      [0],
      [1, 2],
      [0, 2],
      [1, 0],
      [0, 1],
      [2, 1],
      [1, 0, 2],
      [0, 2, 1],
      [0, 1, 2],
      [1, 2, 1],
      [2, 1, 0],
      [0, 1, 0],
      [0, 2, 1, 0],
      [0, 1, 0, 2],
      [1, 2, 1, 0],
      [1, 0, 2, 1],
      [0, 1, 2, 1],
      [0, 1, 0, 2, 1],
      [0, 1, 2, 1, 0],
      [1, 0, 2, 1, 0],
      [0, 1, 0, 2, 1, 0]]]

    Here, the 6 elements of a[0] are the  left  coset representatives of
    the parabolic subgroup generated by 0,1,2,3 (of type A_4); then a[1]
    contains the 5 left  coset representatives of the parabolic subgroup
    generated by 0,1,2 in the previous one;  finally,  a[2] contains all
    24 elements of the parabolic subgroup generated by 0,1,2. Thus,

            { x + y + z | x in a[0], y in a[1], z in a[2] }

    contains each element of W exactly once (where,  as usual in python,
    the '+' denotes concatenation of words).

    See also 'allcoxelms', 'allmats' and 'redleftcosetreps'.
    """
    if len(W.rank) <= 3:
        return [[W.coxelmtoword(c) for c in redleftcosetreps(W)]]

    el = [[W.coxelmtoword(c) for c in redleftcosetreps(W, list(W.rank)[:-1])]]
    for k in range(len(W.rank) - 4):
        J = list(W.rank)[:-k - 1]
        W1 = coxeter([[W.cartan[i][j] for j in J] for i in J])
        el.append([W1.coxelmtoword(c)
                  for c in redleftcosetreps(W1, J[:-1])])
    W1 = coxeter([[W.cartan[i][j] for j in [0, 1, 2]] for i in [0, 1, 2]])
    el.append([W1.coxelmtoword(c) for c in redleftcosetreps(W1)])

    size = 1
    for l in el:
        size *= len(l)
    if size != W.order:
        raise RuntimeError('something went wrong')

    return el


def allelmsproperty(W, f, elm="word", verbose=False):
    """returns  all elements (as reduced expressions in the generators) for
    which a given function f returns True. Here, f takes as argument one
    group element of W, given as a reduced expression.

    This function uses  'allelmchain' so that it is possible to run even
    through all elements of very large groups without first constructing
    a complete list of all elements.

    All elements of order <=2:

    >>> W = coxeter("A",2)
    >>> allelmsproperty(W,lambda x:W.wordtocoxelm(2*x)==(0,1))
    [[], [0], [1], [0, 1, 0]]

    All elements whose reduced expressions contain all generators:

    >>> W = coxeter("B",2)
    >>> allelmsproperty(W,lambda x: set(x)==set([0,1]))
    [[0, 1], [1, 0], [0, 1, 0], [1, 0, 1], [0, 1, 0, 1]]

    See also 'allelmchain'.
    """
    if len(W.rank) <= 5:
        a = (5 - len(W.rank)) * [[[]]] + allelmchain(W)
    else:
        a = allelmchain(W, depth=len(W.rank) - 4)
    if verbose and len(a[0]) > 1:
        print('🄸 (' + str(len(a[4])) + ') ')
    el = []
    for i4 in a[4]:
        if verbose and len(a[0]) > 1:
            print('+')
        for i3 in a[3]:
            for i2 in a[2]:
                e1 = i2 + i3 + i4
                el1 = []
                for i1 in a[1]:
                    for i0 in a[0]:
                        e = i0 + i1 + e1
                        if f(e):
                            el1.append(e)
                el.extend(el1)
    if verbose and len(a[0]) > 1:
        print('\n')
    if verbose:
        print('🄸 Number of elements = ' + str(len(el)) + '\n')
    return el


def allwords(W, maxl=-1):
    """returns all elements of a finite Coxeter group, as reduced
    words, up to a given length. If the optional argument maxl
    is not specified, then all elements will be returned. Each
    w  in the resulting list  is  normalised in the sense that
    w=W.reducedword(w,W).  This function is one of the fastest
    ways to obtain a complete list  of all  elements of W. (It
    uses a call to 'allelmchain'.)

    >>> from pycox import timer
    >>> W = coxeter("E",7);a=timer(allwords,W)   # random
    8.65    # time in seconds
    >>> len(a)
    2903040

    See also 'allbitcoxelms', 'allelmchain', 'allelmsproperty'
    and 'allmats'.
    """
    if maxl == -1:
        maxlen = W.N
    else:
        maxlen = min(maxl, W.N)
    if len(W.rank) <= 5:
        a = (5 - len(W.rank)) * [[[]]] + allelmchain(W)
    else:
        a = allelmchain(W, depth=len(W.rank) - 4)
    el = []
    if maxlen == W.N:
        for i4 in a[4]:
            for i3 in a[3]:
                for i2 in a[2]:
                    e1 = i2 + i3 + i4
                    el1 = []
                    for i1 in a[1]:
                        for i0 in a[0]:
                            el1.append(i0 + i1 + e1)
                    el.extend(el1)
    else:
        for i4 in a[4]:
            for i3 in a[3]:
                for i2 in a[2]:
                    e1 = i2 + i3 + i4
                    el1 = []
                    for i1 in a[1]:
                        for i0 in a[0]:
                            e = i0 + i1 + e1
                            if len(e) <= maxlen:
                                el1.append(e)
                    el.extend(el1)
    el.sort(key=(lambda x: len(x)))
    return el


def allwordslength(W, l=-1):
    """returns all elements of a finite Coxeter group, as reduced
    words, up to a given length. If the optional argument maxl
    is not specified, then all elements will be returned. Each
    w  in the resulting list  is  normalised in the sense that
    w=W.reducedword(w,W).  This function is one of the fastest
    ways to obtain a complete list  of all  elements of W. (It
    uses a call to 'allelmchain'.)

    >>> from pycox import timer
    >>> W = coxeter("E",7);a=timer(allwords,W)  # random
    8.65    # time in seconds
    >>> len(a)
    2903040

    See also 'allbitcoxelms', 'allelmchain', 'allelmsproperty'
    and 'allmats'.
    """
    if l == -1:
        maxlen = W.N
    else:
        maxlen = min(l, W.N)
    if len(W.rank) <= 5:
        a = (5 - len(W.rank)) * [[[]]] + allelmchain(W)
    else:
        a = allelmchain(W, depth=len(W.rank) - 4)
    el = []
    for i4 in a[4]:
        for i3 in a[3]:
            for i2 in a[2]:
                e1 = i2 + i3 + i4
                if len(e1) <= maxlen:
                    el1 = []
                    for i1 in a[1]:
                        for i0 in a[0]:
                            e = i0 + i1 + e1
                            if len(e) == maxlen:
                                el1.append(e)
                    el.extend(el1)
    return el


def allwordstrings(W, maxl=-1):
    """same as allwords but this functions returns strings of reduced
    words.

    >>> from pycox import timer
    >>> W = coxeter("E",7); a=timer(allwordstrings,W)  # random
    3.52    # time in seconds
    >>> len(a)
    2903040

    See also 'allwords', 'allelmsproperty' and 'allmats'.
    """
    if len(W.rank) <= 5:
        a = (5 - len(W.rank)) * [[[]]] + allelmchain(W)
    else:
        a = allelmchain(W, depth=len(W.rank) - 4)
    sa = []
    for ai in a:
        l = ['']
        for w in ai[1:]:
            sw = '.'.join(str(i) for i in w)
            sw += '.'
            l.append(sw)
        sa.append(l)
    el = []
    for i4 in sa[4]:
        for i3 in sa[3]:
            for i2 in sa[2]:
                e1 = i2 + i3 + i4
                el1 = []
                for i1 in sa[1]:
                    for i0 in sa[0]:
                        e = i0 + i1 + e1
                        if e != '' and e[-1] == '.':
                            el1.append(e[:-1])
                        else:
                            el1.append(e)
                el.extend(el1)
    el.sort(key=(lambda x: len(x)))
    return el


def allbitcoxelms(W, maxl=-1, verbose=False):
    """returns all elements of a finite Coxeter group, as coxelm bit
    strings, up to a given length. (Only works in Python 3 and if
    the rank of W is <=8). If the optional argument  maxl is  not
    specified, then all elements will be returned.  A  coxelm bit
    string is the result of applying  the Python function 'bytes'
    to a coxelm. This function is useful (or even essential) when
    it is necessary to deal with all elements of a large group W,
    e.g., type E_7 or E_8.  In type E_7, all the  bitcoxelms will
    fit into 200MB main memory;  for type E_8, 40GB are required.

    See also 'allwords', 'allcoxelms' and 'allmats'.
    """
    if maxl == -1:
        maxlen = W.N
    else:
        maxlen = min(maxl, W.N)
    l = [[bytes(W.rank)]]
    poin = [1]
    ll = longestperm(W)
    if verbose:
        print('🄸 1 ')
    for i in range(maxlen):
        if i < W.N / 2:
            nl = []
            for w in l[i]:
                for s in W.rank:
                    if w[s] < W.N:
                        nl.append(bytes([W.roots.index(tuple([W.roots[w[t]][u] -
                                                              W.cartan[s][t] * W.roots[w[s]][u] for u in W.rank]))
                                         for t in W.rank]))
            l.append(list(set(nl)))
        else:
            l.append([bytes([ll[w[s]] for s in W.rank]) for w in l[W.N - i - 1]])
        poin.append(len(l[i + 1]))
        if verbose:
            print(str(len(l[i + 1])) + ' ')
    if verbose:
        print('\n')
    return l


def allbitwords(W, maxl=-1, verbose=False):
    """returns all elements of  a finite Coxeter group,  as bit word
    strings, up to a given length. (Only works in Python 3 and if
    the rank of W is <=8). If the optional argument  maxl is  not
    specified,  then  all elements will be returned.  A  bit word
    string is the result of applying  the Python function 'bytes'
    to a  word.  This function is useful (or even essential) when
    it is necessary to deal with all elements of a large group W,
    e.g., type E_7 or E_8.

    See also 'allwords', 'allcoxelms' and 'allmats'.
    """
    if maxl == -1:
        maxlen = W.N
    else:
        maxlen = min(maxl, W.N)
    if len(W.rank) <= 5:
        a = (5 - len(W.rank)) * [[[]]] + allelmchain(W)
    else:
        a = allelmchain(W, depth=len(W.rank) - 4)
    el = []
    if verbose:
        print('🄸 ')
    if maxlen == W.N:
        for i4 in a[4]:
            if verbose:
                print('+')
            for i3 in a[3]:
                for i2 in a[2]:
                    e1 = i2 + i3 + i4
                    el1 = []
                    for i1 in a[1]:
                        for i0 in a[0]:
                            el1.append(bytes(i0 + i1 + e1))
                    el.extend(el1)
    else:
        for i4 in a[4]:
            if verbose:
                print('+')
            for i3 in a[3]:
                for i2 in a[2]:
                    e1 = i2 + i3 + i4
                    el1 = []
                    for i1 in a[1]:
                        for i0 in a[0]:
                            e = i0 + i1 + e1
                            if len(e) <= maxlen:
                                el1.append(bytes(e))
                    el.extend(el1)
    if verbose:
        print('\n')
    el.sort(key=(lambda x: len(x)))
    return el

# F longestcoxelm1 (for use in coxeterclasses)


def longestcoxelm1(W, J):
    m = idmat(W.rank, 1)
    weiter = True
    while weiter:
        s = 0
        while s < len(J) and all(m[J[s]][t] <= 0 for t in W.rank):
            s += 1
        if s < len(J):
            m = [[m[t][u] - W.cartan[J[s]][t] * m[J[s]][u]
                  for u in W.rank] for t in W.rank]
        else:
            weiter = False
    # return tuple([W.roots.index(tuple(l)) for l in m])
    return [W.roots.index(tuple(m[s])) - W.N for s in J]

# F longestcoxelm (for use in coxeterclasses)


def longestcoxelm(W, J):
    if W.cartantype[0][0] == 'U':
        return J
    rgJ = range(len(J))
    m = idmat(rgJ, 1)
    weiter = True
    while weiter:
        s = 0
        while s < len(J) and all(m[s][t] <= 0 for t in rgJ):
            s += 1
        if s < len(J):
            m = [[m[t][u] - W.cartan[J[s]][J[t]] * m[s][u]
                  for u in rgJ] for t in rgJ]
        else:
            weiter = False
    return [J[l.index(-1)] for l in m]


def w0conjugation(cmat):
    """returns the permutations of the simple reflections induced by
    conjugation with the  longest element in the  finite  Coxeter
    group corresponding to the given Cartan matrix.
    """
    p = list(range(len(cmat)))
    if not p:
        return []
    for l1 in decomposemat(cmat):
        t = finitetypemat([[cmat[i][j] for j in l1] for i in l1])
        t1 = [l1[i] for i in t[1]]
        if t[0] == 'A':
            pt = t1[::-1]
            for i in range(len(t1)):
                p[t1[i]] = pt[i]
        if t[0] == 'D' and len(t1) % 2:
            x = t1[0]
            p[t1[0]] = t1[1]
            p[t1[1]] = x
        if t[0] == 'E' and len(t1) == 6:
            x = t1[0]
            p[t1[0]] = t1[5]
            p[t1[5]] = x
            y = t1[2]
            p[t1[2]] = 4
            p[t1[4]] = y
        if t[0][0] == 'I' and int(t[0][-1]) % 2:
            x = t1[0]
            p[t1[0]] = t1[1]
            p[t1[1]] = x
    return p


def coxeterclasses(W):
    """returns a dictionary with information about the Coxeter classes
    of subsets of S, where S denotes the set of  simple reflections
    of W.  Let I,J be subsets of S.  Then I,J are said to belong to
    the same Coxeter class if and only if there exists some  w in W
    such that J = {wsw^-1 | s in I}.  This relation can be computed
    using the  algorithm described in  [Ge-Pf, 2.3.3].  The various
    subsets of S are described by bit strings.

    >>> coxeterclasses(coxeter("A",3))         #I 5 coxeter classes
    {'000': {'J': [], 'class': 0, 'w0J': [0, 1, 2]},
     '001': {'J': [2], 'class': 1, 'w0J': [0, 1, 2]},
     '010': {'J': [1], 'class': 1, 'w0J': [0, 1, 2]},
     '011': {'J': [1, 2], 'class': 2, 'w0J': [0, 2, 1]},
     '100': {'J': [0], 'class': 1, 'w0J': [0, 1, 2]},
     '101': {'J': [0, 2], 'class': 3, 'w0J': [0, 1, 2]},
     '110': {'J': [0, 1], 'class': 2, 'w0J': [1, 0, 2]},
     '111': {'J': [0, 1, 2], 'class': 4, 'w0J': [2, 1, 0]},
     'coxclassreps': ['000', '100', '110', '101', '111']}

    Thus, the bit strings  '010','011','001',.... correspond to the
    subsets [1],[1,2],[2],... of S=[0,1,2]. Representatives for the
    various Coxeter classes are given in  'coxclassreps'.  An entry
    'class':i means that the given subset belongs to the class with
    representative coxclassreps[i]. In the above example (type An),
    Coxeter classes correspond to the partitions of n+1.
    """
    try:
        return W.coxeterclasses
    except AttributeError:
        pass
    W.coxeterclasses = {}
    rest = []
    for s in cartesian(len(W.rank) * [[0, 1]]):
        Jb = ''
        subs = []
        for i in range(len(s)):
            if s[i] == 0:
                Jb += '0'
            else:
                Jb += '1'
                subs.append(i)
        if len(subs) > 8:
            w0 = [subs[s] for s in w0conjugation([[W.cartan[k][l]
                                                   for l in subs] for k in subs])]
        else:
            w0 = longestcoxelm(W, subs)
        p0 = list(W.rank)
        for i in range(len(subs)):
            # p0[i]=w0[i]-W.N
            p0[subs[i]] = w0[i]
        W.coxeterclasses[Jb] = {'J': subs[:], 'w0J': p0[:]}
        rest.append(Jb)
    classes = []
    numb = 0
    while rest:
        orb = [rest[0]]
        rest.remove(orb[0])
        for subs in orb:
            for s in W.rank:
                if subs[s] == '0':
                    l = list(subs)
                    l[s] = '1'
                    bigsub = ''.join(l)
                    if W.coxeterclasses[bigsub]['w0J'] != W.rank:
                        nsubs = ''.join(subs[i]
                                        for i in W.coxeterclasses[bigsub]['w0J'])
                        if nsubs not in orb:
                            orb.append(nsubs)
                            rest.remove(nsubs)
        orb.sort(reverse=True)
        classes.append(orb[0])
        for subs in orb:
            W.coxeterclasses[subs]['class'] = numb
        numb += 1
    W.coxeterclasses['coxclassreps'] = classes[:]
    return W.coxeterclasses


def conjclassdata(typ, n):
    """returns representatives of minimal length for all the conjugacy
    classes of the finite Coxeter group of type 'typ' and rank 'n'.

    The data are taken from the corresponding files in gap-chevie.
    """
    reps = []
    names = []
    cents = []
    if typ[0] == 'A':
        for mu in partitions(n + 1):
            w = []
            i = 0
            for l in mu:
                w.extend(range(i + 1, i + l))
                i = i + l
            reps.append(w)
            cents.append(centraliserpartition(n + 1, mu))
            if n > 0:
                names.append(str(mu))
            else:
                names.append(' ')
    if typ[0] == 'B' or typ[0] == 'C':
        if n == 2 and typ[0] == 'B':
            reps = [[], [2], [2, 1, 2, 1], [1], [2, 1]]
            cents = [8, 4, 8, 4, 4]
            names = [str([[1, 1], []]), str([[1], [1]]), str([[], [1, 1]]),
                     str([[2], []]), str([[], [2]])]
        elif n == 2 and typ[0] == 'C':
            reps = [[], [1], [1, 2, 1, 2], [2], [1, 2]]
            cents = [8, 4, 8, 4, 4]
            names = [str([[1, 1], []]), str([[1], [1]]), str([[], [1, 1]]),
                     str([[2], []]), str([[], [2]])]
        else:
            reps = []
            for mu in partitiontuples(n, 2):
                w = []
                i = 1
                for l in mu[1][::-1]:  # reversed list
                    # w.extend(range(2,i+1)[::-1])
                    w.extend(range(i, 1, -1))
                    w.extend(range(1, i + l))
                    i = i + l
                for l in mu[0]:
                    w.extend(range(i + 1, i + l))
                    i = i + l
                reps.append(w)
                cents.append(centralisertuple(n, 2, mu))
                names.append(str(mu))
    if typ[0] == 'D':
        reps = []
        for mu in partitiontuples(n, 2):
            if len(mu[1]) % 2 == 0:
                w = []
                i = 1
                for l in mu[1][::-1]:
                    if i == 1:
                        w.extend(range(2, i + l))
                    else:
                        # w.extend(range(3,i+1)[::-1])
                        w.extend(range(i, 2, -1))
                        w.extend(range(1, i + l))
                    i = i + l
                for l in mu[0]:
                    w.extend(range(i + 1, i + l))
                    i = i + l
                if w != [] and w[0] == 2:
                    w[0] = 1
                cent = centralisertuple(n, 2, mu)
                if not mu[1] and all(x % 2 == 0 for x in mu[0]):
                    reps.append(w)
                    cents.append(cent)
                    names.append('[' + str(mu[0]) + ', +]')
                    w1 = w[:]
                    w1[0] = 2
                    reps.append(w1)
                    cents.append(cent)
                    names.append('[' + str(mu[0]) + ', -]')
                else:
                    reps.append(w)
                    cents.append(cent // 2)
                    names.append(str(mu))
    if typ[0] == 'G':
        reps = [[], [2], [1], [1, 2], [1, 2, 1, 2], [1, 2, 1, 2, 1, 2]]
        cents = [12, 4, 4, 6, 6, 12]
        names = [" ", "~A_1", "A_1", "G_2", "A_2", "A_1+~A_1"]
    if typ[0] == 'F':
        reps = [[], [1, 2, 1, 3, 2, 1, 3, 2, 3, 4, 3, 2, 1, 3, 2, 3, 4, 3, 2, 1, 3, 2, 3, 4], [2, 3, 2, 3],
                [2, 1], [2, 3, 2, 3, 4, 3, 2, 1, 3, 4], [3, 2, 4, 3, 2, 1, 3, 2, 4, 3, 2, 1], [4, 3],
                [1, 2, 1, 4, 3, 2, 1, 3, 2, 3], [3, 2, 1, 4, 3, 2, 1, 3, 2, 3, 4, 3, 2, 1, 3, 2],
                [3, 2, 4, 3, 2, 1, 3, 2], [4, 3, 2, 1], [1], [2, 3, 2, 3, 4, 3, 2, 3, 4], [1, 4, 3], [4, 3, 2],
                [2, 3, 2, 1, 3], [3], [1, 2, 1, 3, 2, 1, 3, 2, 3], [
            2, 1, 4], [3, 2, 1], [2, 4, 3, 2, 3], [1, 3],
            [3, 2], [2, 3, 2, 3, 4, 3, 2, 1, 3, 2, 4, 3, 2, 1], [2, 4, 3, 2, 1, 3]]
        cents = [1152, 1152, 64, 36, 36, 96, 36, 36, 72, 72, 12, 96, 96, 12, 12, 16, 96, 96, 12,
                 12, 16, 16, 32, 32, 8]
        names = [" ", "4A_1", "2A_1", "A_2", "D_4", "D_4(a_1)", "~A_2", "C_3+A_1",
                 "A_2+~A_2", "F_4(a_1)", "F_4", "A_1", "3A_1", "~A_2+A_1", "C_3", "A_3",
                 "~A_1", "2A_1+~A_1", "A_2+~A_1", "B_3", "B_2+A_1", "A_1+~A_1", "B_2",
                 "A_3+~A_1", "B_4"]
    if typ[0] == 'E' and n == 6:
        reps = [[], [3, 4, 3, 2, 4, 3, 5, 4, 3, 2, 4, 5], [1, 4],
                [1, 3, 1, 4, 3, 1, 2, 4, 5, 4, 3, 1, 2, 4, 3, 5, 6, 5, 4, 3, 2, 4, 5, 6], [1, 3], [1, 3, 5, 6],
                [3, 4, 3, 2, 4, 5], [1, 4, 3, 6], [1, 4, 3, 2], [
            1, 2, 3, 1, 5, 4, 6, 5, 4, 2, 3, 4], [3, 4, 2, 5],
            [1, 2, 3, 4, 2, 3, 4, 6, 5, 4, 2, 3, 4, 5], [1, 3, 2, 5], [1, 3, 4, 3, 2, 4, 5, 6],
            [1, 4, 6, 2, 3, 5], [1], [1, 4, 6], [1, 3, 4, 3, 2, 4, 3, 5, 4, 3, 2, 4, 5], [1, 4, 3], [1, 3, 2],
            [1, 3, 2, 5, 6], [1, 4, 6, 3, 5], [1, 3, 4, 2, 5], [1, 4, 3, 2, 6], [1, 4, 2, 5, 4, 2, 3]]
        cents = [51840, 1152, 192, 648, 216, 108, 96, 16, 10, 72, 36, 36, 24, 9, 12, 1440, 96,
                 96, 32, 36, 36, 12, 8, 10, 12]
        names = [" ", "4A_1", "2A_1", "3A_2", "A_2", "2A_2", "D_4(a_1)", "A_3+A_1",
                 "A_4", "E_6(a_2)", "D_4", "A_5+A_1", "A_2+2A_1", "E_6(a_1)", "E_6", "A_1",
                 "3A_1", "A_3+2A_1", "A_3", "A_2+A_1", "2A_2+A_1", "A_5", "D_5", "A_4+A_1",
                 "D_5(a_1)"]
    if typ[0] == 'E' and n == 7:
        reps = [[], [7, 6, 7, 5, 6, 7, 4, 5, 6, 7, 2, 4, 5, 6, 7, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3],
                [5, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3], [7, 5], [7, 5, 2, 3], [7, 6],
                [6, 5, 6, 4, 5, 6, 2, 4, 3, 4, 5, 6, 2, 4, 5, 3, 1, 3, 4, 5, 2, 4, 3, 1], [7, 6, 4, 2],
                [5, 4, 5, 2, 4, 3], [7, 5, 6, 2], [7, 5, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3, 1],
                [7, 6, 7, 5, 6, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3], [7, 5, 6, 3], [7, 6, 5, 4],
                [7, 6, 5, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3], [5, 4, 2, 3], [1, 2, 3, 1, 5, 4, 6, 5, 4, 2, 3, 4],
                [7, 6, 4, 1], [7, 6, 7, 5, 6, 4, 5, 2, 4, 3], [1, 2, 3, 4, 2, 3, 4, 6, 5, 4, 2, 3, 4, 5],
                [7, 5, 2, 6, 4, 1], [7, 6, 5, 4, 3, 1], [7, 5, 2, 3, 4, 1], [3, 4, 2, 3, 4, 7, 6, 5],
                [6, 5, 4, 5, 2, 4, 3, 1], [7, 6, 5, 4, 2, 3], [7, 5, 6, 2, 3, 1], [7, 5, 4, 5, 2, 4, 3, 1],
                [6, 4, 1, 5, 3, 2], [7, 6, 4, 2, 3, 1],
                [7, 6, 7, 5, 6, 7, 4, 5, 6, 7, 2, 4, 5, 6, 7, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3, 1,
                 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3, 1, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3, 1],
                [7], [7, 5, 2], [7, 5, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3], [7, 5, 3],
                [7, 6, 7, 5, 6, 7, 4, 5, 6, 7, 2, 4, 5, 6, 7, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3, 1],
                [7, 6, 7, 5, 6, 7, 4, 5, 6, 2, 4, 3, 4, 5, 2, 4, 3, 1, 3, 4, 2],
                [7, 6, 7, 5, 6, 4, 5, 6, 2, 4, 5, 6, 3, 4, 5, 6, 1, 3, 4, 5, 2, 4, 3],
                [7, 6, 7, 5, 6, 7, 4, 5, 6, 7, 2, 4, 5, 6, 7, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 1, 3, 4, 5, 2, 4, 3, 1],
                [6, 5, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3], [7, 5, 6], [7, 5, 4, 5, 2, 4, 3], [7, 5, 6, 2, 3],
                [7, 6, 5, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3, 1], [7, 6, 4], [7, 5, 2, 3, 1],
                [7, 6, 5, 6, 4, 5, 6, 2, 4, 3, 4, 5, 6, 2, 4, 5, 3, 1, 3, 4, 5, 2, 4, 3, 1], [7, 5, 4, 2, 3],
                [7, 6, 4, 2, 1], [7, 5, 2, 6, 4], [7, 5, 3, 6, 4], [7, 6, 5, 4, 5, 2, 4, 3, 1], [6, 5, 4, 2, 3],
                [7, 6, 7, 5, 6, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3, 1], [7, 6, 5, 4, 2, 3, 1], [7, 5, 6, 4, 1],
                [3, 4, 2, 3, 4, 6, 5], [7, 5, 6, 3, 1], [7, 6, 7, 5, 6, 4, 5, 2, 4, 3, 1],
                [2, 4, 2, 3, 5, 4, 2, 7, 6, 5, 4, 3, 1]]
        cents = [2903040, 46080, 9216, 3072, 768, 4320, 1296, 216, 768, 384, 384, 256, 64,
                 60, 288, 288, 144, 96, 72, 72, 24, 14, 32, 32, 18, 20, 48, 48, 24, 30, 2903040,
                 46080, 9216, 3072, 768, 4320, 1296, 216, 768, 384, 384, 256, 64, 60, 288,
                 288, 144, 96, 72, 72, 24, 14, 32, 32, 18, 20, 48, 48, 24, 30]
        names = [" ", "6A_1", "4A_1''", "2A_1", "4A_1'", "A_2", "3A_2", "2A_2", "D_4(a_1)",
                 "A_3+A_1'", "A_3+3A_1", "D_4(a_1)+2A_1", "A_3+A_1''", "A_4", "D_4+2A_1",
                 "D_4", "E_6(a_2)", "A_2+2A_1", "D_6(a_2)", "A_5+A_1''", "A_5+A_1'", "A_6",
                 "D_5+A_1", "D_6(a_1)", "E_6(a_1)", "D_6", "A_3+A_2+A_1", "D_5(a_1)+A_1",
                 "E_6", "A_4+A_2", "7A_1", "A_1", "3A_1'", "5A_1", "3A_1''", "D_4+3A_1",
                 "E_7(a_4)", "D_6(a_2)+A_1", "2A_3+A_1", "A_3+2A_1''", "A_3",
                 "D_4(a_1)+A_1", "A_3+2A_1'", "D_6+A_1", "A_2+A_1", "A_2+3A_1", "A_5+A_2",
                 "D_4+A_1", "2A_2+A_1", "A_5'", "A_5''", "E_7(a_1)", "D_5", "A_7", "E_7",
                 "A_4+A_1", "D_5(a_1)", "A_3+A_2", "E_7(a_2)", "E_7(a_3)"]
    if typ[0] == 'E' and n == 8:
        reps = [[], [8, 7, 8, 6, 7, 8, 5, 6, 7, 8, 4, 5, 6, 7, 8, 2, 4, 5, 6, 7, 8, 3, 4, 5, 6, 7, 8, 2, 4, 5,
                     6, 7, 3, 4, 5, 6, 2, 4, 5, 3, 4, 2, 1, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 7, 3, 4, 5, 6, 2, 4, 5, 3, 4, 2,
                     1, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 7, 3, 4, 5, 6, 2, 4, 5, 3, 4, 2, 1, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 3,
                     4, 5, 2, 4, 3, 1, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3, 1],
                [5, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3], [6, 1],
                [7, 6, 7, 5, 6, 7, 4, 5, 6, 7, 2, 4, 5, 6, 7, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3],
                [8, 7, 6, 7, 5, 6, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 3, 4, 5, 1, 3, 4, 5, 6, 7, 8,
                 2, 4, 5, 6, 7, 3, 4, 5, 6, 2, 4, 5, 3, 4, 2, 1, 3, 4, 5, 6, 7, 2, 4, 5, 3, 1], [7, 5, 2, 3], [6, 7],
                [1, 2, 3, 1, 4, 2, 3, 1, 4, 3, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4,
                 3, 1, 7, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 3, 1, 7, 6, 5, 4, 2, 3, 4, 5, 6, 7, 8],
                [8, 7, 8, 6, 7, 5, 6, 7, 4, 2, 4, 5, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 3, 4, 5, 2, 1, 3, 4, 5, 6, 7, 8, 2,
                 4, 5, 6, 7, 3, 4, 5, 6, 2, 4, 5, 3, 4, 1, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 7, 3, 4, 5, 6, 2, 4, 5, 3, 4,
                 2, 1, 3, 4, 5, 6, 2, 4, 5, 3, 4, 1],
                [5, 6, 4, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 3, 4, 2, 1, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 7, 3, 4, 5, 2, 1, 3,
                 4, 5, 6, 7, 8, 2], [6, 5, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3, 1, 3, 4, 5, 6, 2, 4, 5, 3, 4, 1, 3],
                [2, 3, 4, 2, 3, 4, 5, 4, 2, 3, 1, 4, 5, 6, 8, 7, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 3, 1, 7, 6,
                 5, 4, 2, 3, 4, 5, 6, 7], [7, 8, 2, 4], [2, 4, 2, 5, 4, 2, 6, 5, 4, 2, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3,
                                                         4, 5, 6, 7, 8, 7, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 3, 1, 7, 8], [4, 2, 4, 3, 4, 5],
                [1, 2, 3, 1, 4, 2, 3, 1, 4, 3, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4,
                 3, 1, 7, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 3, 1, 7, 8, 7, 6, 5, 4, 2, 3, 4, 5, 6, 7, 8],
                [2, 3, 4, 2, 3, 4, 6, 5, 7, 6, 5, 4, 2, 3, 4, 5], [3, 7, 6, 8],
                [1, 2, 3, 4, 2, 3, 4, 5, 4, 2, 3, 4, 5, 7], [4, 5, 6, 7, 3, 4, 5, 2, 4, 3, 1, 3, 4, 5, 6, 7, 8, 2, 4,
                                                             5, 3, 4, 2, 1, 3, 4, 5, 6, 7, 8], [7, 6, 8, 1, 4, 3], [5, 6, 3, 4],
                [3, 4, 3, 5, 4, 3, 6, 5, 4, 3, 8, 7, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 3, 7, 6, 5, 4, 2],
                [7, 5, 6, 2, 4, 5, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 7, 1, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 7, 3, 4, 5, 2, 4,
                 3, 1, 3, 4, 5, 6, 7, 8, 2, 4, 5, 6, 3, 4],
                [8, 7, 6, 7, 5, 4, 5, 6, 2, 4, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 4, 5, 3],
                [8, 7, 5, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3], [5, 4, 2, 3], [1, 2, 3, 1, 4, 2, 3, 1, 4, 5, 4, 2, 3, 1,
                                                                           4, 3, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 3, 1, 7, 6, 5, 4, 2, 3, 4, 5, 6, 7, 8, 7],
                [7, 4, 5, 1], [5, 4, 5, 2, 4, 5, 3, 4, 5, 6, 7, 2, 4, 3],
                [8, 7, 6, 7, 5, 2, 4, 3, 4, 5, 2, 4, 1, 3, 4, 5, 6, 2, 4, 5], [3, 4, 2, 3, 5, 4, 2, 3, 1, 4, 5, 6],
                [4, 3, 5, 4, 2, 3, 4, 5, 6, 5, 4, 2, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 2, 3, 1,
                 4, 3, 5, 4, 2, 6, 5, 4, 3, 1, 7, 8], [2, 3, 4, 2, 3, 4, 5, 4, 2, 3, 1, 4, 5, 6], [8, 7, 5, 2, 4, 3],
                [7, 8, 5, 2, 3, 1], [6, 5, 6, 7, 4, 2, 4, 5, 3, 4],
                [5, 4, 6, 5, 4, 2, 3, 7, 6, 5, 4, 2, 3, 8, 7, 6, 5, 4, 2, 3, 1, 4], [6, 4, 5, 2, 7, 1],
                [8, 5, 6, 7, 2, 4], [2, 7, 6, 5, 4, 2, 3, 4, 8, 7, 6, 5, 4, 2, 3, 1, 4, 3], [8, 5, 6, 2, 3, 4],
                [2, 4, 2, 3, 4, 5, 6, 7],
                [2, 4, 2, 5, 4, 2, 3, 6, 5, 4, 2, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 3, 1, 7, 8],
                [5, 3, 4, 5, 6, 2, 4, 1], [3, 4, 3, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 8, 7, 6],
                [1, 3, 4, 3, 1, 5, 4, 2, 3, 4, 5, 8, 7, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 7, 6],
                [2, 3, 4, 3, 1, 5, 4, 2, 3, 4, 5, 6, 7, 8], [6, 7, 8, 5, 2, 1], [7, 5, 6, 2, 3, 4],
                [6, 7, 8, 5, 6, 7, 4, 5, 3, 4, 2, 1], [7, 8, 4, 2, 3, 4, 5, 2],
                [1, 3, 1, 4, 5, 4, 3, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 7, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 2, 6, 5, 4, 3,
                 1, 7, 6, 5, 4, 2, 3, 4, 5, 6, 7, 8],
                [1, 2, 3, 4, 2, 3, 1, 4, 3, 5, 4, 2, 3, 1, 4, 5, 6, 5, 4, 2, 3, 4, 5, 6, 8, 7],
                [1, 2, 3, 1, 4, 2, 5, 4, 2, 3, 1, 4, 6, 5, 4, 2, 3, 4, 5, 6, 7, 8], [6, 4, 1, 5, 3, 2],
                [1, 2, 3, 1, 4, 2, 3, 1, 4, 3, 5, 4, 3, 1, 6, 5, 4, 2, 3, 4, 5, 6, 7, 8], [5, 7, 6, 2, 1, 3],
                [8, 1, 2, 3, 4, 2, 5, 4], [8, 7, 6, 2, 4, 5, 3, 4, 1, 3], [8, 7, 6, 5, 3, 1],
                [3, 4, 2, 3, 5, 4, 2, 3, 4, 6, 5, 4, 2, 3, 7, 6, 5, 4, 2, 3, 1, 4, 5, 6, 7, 8],
                [8, 6, 5, 4, 2, 3, 4, 5, 6, 7, 1, 3, 4, 5, 2, 4], [7, 8, 6, 2, 1, 3, 4, 5], [3],
                [7, 6, 7, 5, 6, 7, 4, 5, 6, 7, 2, 4, 5, 6, 7, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3, 1, 3, 4, 5,
                 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3, 1, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 2, 4, 3, 1], [8, 6, 1],
                [7, 5, 4, 5, 2, 4, 5, 3, 4, 5, 2, 4, 3], [4, 1, 3],
                [2, 3, 4, 2, 3, 4, 5, 4, 2, 3, 4, 5, 6, 5, 4, 2, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 4, 5, 6, 7, 8],
                [2, 3, 4, 2, 3, 4, 5, 4, 2, 3, 4, 5, 6], [8, 5, 4, 2, 3, 4, 2],
                [2, 4, 2, 3, 4, 5, 4, 2, 3, 1, 4, 3, 5, 6, 5, 4, 2, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 1, 4, 3, 5, 6, 7],
                [2, 3, 4, 5, 4, 2, 3, 4, 5, 7, 6, 8, 7, 6, 5, 4, 2, 3, 4, 5, 6], [8, 5, 2, 4, 1], [4, 2, 1],
                [2, 3, 4, 2, 3, 4, 5, 4, 2, 3, 4, 5, 6, 5, 4, 2, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 1, 4, 5, 6, 7],
                [8, 5, 6, 4, 5, 6, 3, 4, 5, 6, 2, 4, 3, 1, 3, 4, 5, 6, 2, 4, 5, 3, 4, 2, 1],
                [5, 2, 4, 5, 1, 3, 4, 5, 6, 2, 4, 5, 3, 4, 2, 1, 3, 4, 5, 6, 7], [8, 5, 2, 3, 1], [7, 5, 4, 2, 3],
                [8, 6, 5, 3, 1], [2, 3, 4, 2, 3, 1, 4, 5, 4, 2, 6, 5, 4, 2, 3, 1, 4, 3, 5, 4, 6, 5, 7],
                [1, 2, 3, 1, 4, 2, 3, 5, 4, 2, 3, 1, 4, 3, 5, 4, 6, 5, 4, 2, 3, 4, 5, 6, 7],
                [1, 2, 3, 4, 2, 6, 5, 4, 2, 3, 4, 5, 8], [7, 5, 2, 6, 4],
                [8, 2, 3, 4, 2, 3, 4, 5, 4, 2, 3, 1, 4, 5, 6], [2, 3, 5, 1, 4],
                [2, 3, 4, 2, 3, 4, 5, 4, 2, 3, 4, 5, 7, 6, 8], [2, 3, 5, 6, 5, 4, 2, 3, 4, 7, 6, 5, 4, 2, 3, 1, 4],
                [4, 6, 8, 1, 3, 5, 7], [5, 6, 2, 4, 1], [6, 7, 5, 4, 5, 2, 4, 5, 1, 3, 4, 5, 2, 4, 3],
                [2, 3, 4, 2, 3, 4, 5, 4, 2, 3, 1, 4, 5, 8, 7], [4, 2, 5, 4, 2, 3, 1], [7, 6, 4, 2, 3],
                [2, 3, 4, 2, 3, 4, 5, 7, 6, 5, 4, 2, 3, 4, 5, 6, 8], [1, 4, 2, 5, 4, 2, 3, 7, 8],
                [6, 7, 8, 5, 4, 2, 3], [8, 6, 4, 1, 2, 3, 5], [4, 2, 5, 4, 3, 1, 6, 5, 7, 6, 5],
                [8, 6, 7, 2, 4, 5, 1], [5, 3, 4, 5, 6, 7, 2, 4, 1], [8, 5, 6, 3, 4, 2, 1, 3, 4],
                [6, 7, 5, 2, 4, 3, 1], [8, 6, 7, 4, 1, 2, 3], [7, 8, 5, 6, 4, 2, 4, 3, 4], [7, 8, 4, 5, 2, 3, 1],
                [4, 3, 5, 4, 2, 3, 4, 5, 6, 8, 7], [8, 6, 7, 5, 2, 3, 1], [2, 4, 2, 3, 1, 6, 5, 4, 2, 3, 4, 5, 7]]
        cents = [696729600, 696729600, 221184, 184320, 184320, 46080, 6144, 311040,
                 311040, 155520, 155520, 7776, 7776, 2592, 2592, 18432, 18432, 1024, 768,
                 768, 192, 128, 1200, 1200, 600, 600, 6912, 6912, 1728, 1152, 1152, 288, 864,
                 864, 432, 216, 288, 288, 72, 48, 28, 28, 64, 128, 128, 108, 108, 54, 54, 80, 80,
                 20, 576, 576, 288, 288, 144, 144, 96, 96, 24, 60, 60, 30, 30, 5806080, 5806080,
                 18432, 18432, 15360, 15360, 4608, 1536, 1536, 768, 256, 8640, 8640, 2592,
                 2592, 576, 576, 432, 432, 288, 288, 144, 144, 384, 384, 64, 16, 120, 120, 576,
                 576, 192, 192, 72, 24, 48, 48, 28, 28, 36, 36, 40, 40, 48, 48, 60, 60]
        names = [" ", "8A_1", "4A_1'", "2A_1", "6A_1", "2D_4(a_1)", "4A_1''", "A_2",
                 "D_4+4A_1", "4A_2", "E_8(a_8)", "3A_2", "E_7(a_4)+A_1", "2A_2", "2D_4",
                 "D_4(a_1)", "2A_3+2A_1", "2A_3'", "A_3+A_1", "A_3+3A_1", "D_8(a_3)",
                 "2A_3''", "A_4", "D_6+2A_1", "2A_4", "E_8(a_6)", "A_2+4A_1", "D_4",
                 "E_6(a_2)+A_2", "A_2+2A_1", "D_4+2A_1", "E_8(a_3)", "E_6(a_2)",
                 "A_5+A_2+A_1", "A_5+A_1'", "D_4+A_2", "2A_2+2A_1", "D_6(a_2)", "D_8(a_1)",
                 "A_5+A_1''", "A_6", "D_8", "D_5+A_1", "D_6(a_1)", "A_7+A_1", "E_6(a_1)",
                 "E_7+A_1", "A_8", "E_8(a_4)", "A_4+2A_1", "D_6", "E_8(a_2)",
                 "D_4(a_1)+A_2", "D_5(a_1)+A_3", "E_6+A_2", "E_8(a_7)", "E_6",
                 "E_7(a_2)+A_1", "A_3+A_2+A_1", "D_5(a_1)+A_1", "E_8(a_1)", "A_4+A_2",
                 "D_8(a_2)", "E_8(a_5)", "E_8", "A_1", "7A_1", "3A_1", "5A_1", "A_3",
                 "A_3+4A_1", "A_3+2A_1'", "D_4(a_1)+A_1", "2A_3+A_1", "D_4(a_1)+A_3",
                 "A_3+2A_1''", "A_2+A_1", "D_4+3A_1", "3A_2+A_1", "E_7(a_4)", "A_2+3A_1",
                 "D_4+A_1", "2A_2+A_1", "D_6(a_2)+A_1", "A_5+A_2", "E_6(a_2)+A_1", "A_5",
                 "A_5+2A_1", "D_5", "D_5+2A_1", "A_7'", "A_7''", "A_4+A_1", "D_6+A_1",
                 "A_3+A_2+2A_1", "D_5(a_1)", "A_3+A_2", "D_4+A_3", "D_5(a_1)+A_2", "D_7",
                 "E_6+A_1", "E_7(a_2)", "A_6+A_1", "E_7(a_1)", "E_6(a_1)+A_1", "E_7",
                 "A_4+A_3", "D_7(a_1)", "D_5+A_2", "D_7(a_2)", "A_4+A_2+1", "E_7(a_3)"]
    if typ[0] == 'H' and n == 3:
        reps = [[], [1], [1, 2], [1, 3], [2, 3], [1, 2, 3], [1, 2, 1, 2], [1, 2, 1, 2, 3],
                [1, 2, 1, 2, 3, 2, 1, 2, 3], [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3]]
        cents = [120, 8, 10, 8, 6, 10, 10, 6, 10, 120]
    if typ[0] == 'H' and n == 4:
        reps = [[], [1], [1, 2], [1, 3], [2, 3], [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 4, 3],
                [1, 2, 1, 2], [1, 2, 3, 4], [1, 2, 1, 2, 3], [1, 2, 1, 2, 4], [1, 2, 1, 2, 3, 4],
                [1, 2, 3, 2, 1, 2, 3, 4], [1, 2, 1, 2, 3, 2, 1, 2, 3], [1, 2, 1, 2, 3, 2, 1, 2, 3, 4],
                [1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4], [1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3], [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 3, 4],
                [1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4],
                [2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3,
                 2, 1, 2, 1, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3,
                 2, 1, 2, 1, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2, 1, 2, 1,
                 3, 2, 1, 4, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2,
                 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4],
                [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2,
                 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4]]
        cents = [14400, 240, 100, 32, 36, 20, 20, 12, 8, 100, 30, 12, 20, 20, 30, 20, 12, 600,
                 50, 240, 100, 30, 20, 360, 36, 600, 50, 30, 240, 600, 100, 360, 600, 14400]
    if typ[0] == 'I':
        cl = [1]
        m = int(typ[1:])
        if m % 2 == 0:
            reps = [[], [1], [2]]
            cl.extend([m // 2, m // 2])
            x = [1, 2]
            for i in range(1, m // 2 + 1):
                reps.append(x[:])
                cl.append(2)
                x.extend([1, 2])
            cl[-1] = 1
        else:
            reps = [[], [1]]
            cl.append(m)
            x = [1, 2]
            for i in range(1, (m - 1) // 2 + 1):
                reps.append(x[:])
                cl.append(2)
                x.extend([1, 2])
        cents = [2 * m // c for c in cl]
    if not names:
        for w in reps:
            if not w:
                names.append(' ')
            else:
                nn = str(w[0])
                for i in w[1:]:
                    nn += str(i)
                names.append(nn)
    return {'reps': [[s - 1 for s in w] for w in reps],
            'centralisers': cents[:], 'names': names[:]}


def conjugacyclasses(W):
    """returns  representatives  of   minimal length  in the  conjugacy
    classes of W. The result is a dictionary with entries:

    - reps          -- list of representatives of minimal length
    - classlengths  -- list of sizes of conjugacy classes
    - classnames    -- list of tuples of names for the classes put
      together from the irreducible components of W

    The conventions  are the same as in  gap-chevie;  in particular,
    the  ordering  of the  classes is the same as in gap-chevie.

    The raw data for the various types of irreducible finite Coxeter
    groups are explicitly  stored in this module and called  via the
    function 'conjclassdata(typ,rank)'. For a general finite Coxeter
    group W the data  are then built  together from the  irreducible
    components using 'W.cartantype'.

    >>> conjugacyclasses(coxeter("G",2))
    {'classlengths': [1, 3, 3, 2, 2, 1],
     'classnames': [(' ',),
      ('~A_1',),
      ('A_1',),
      ('G_2',),
      ('A_2',),
      ('A_1+~A_1',)],
     'reps': [[], [1], [0], [0, 1], [0, 1, 0, 1], [0, 1, 0, 1, 0, 1]]}

    >>> W = coxeter([[2,0,-1,0],[0,2,0,-2],[-1,0,2,0],[0,-1,0,2]])
    >>> W.cartantype
    [['A', [0, 2]], ['C', [3, 1]]]
    >>> conjugacyclasses(W)['reps']
    [[],
     [3],
     [3, 1, 3, 1],
     [1],
     [3, 1],
     [0],
     [0, 3],
     [0, 3, 1, 3, 1],
     [0, 1],
     [0, 3, 1],
     [0, 2],
     [0, 2, 3],
     [0, 2, 3, 1, 3, 1],
     [0, 2, 1],
     [0, 2, 3, 1]]

    The representatives of the classes are ``good`` in the sense of::

        M. Geck and J. Michel, Good elements in finite Coxeter
        groups and representations of Iwahori--Hecke algebras,
        Proc. London Math. Soc. (3) 74 (1997), 275-305.

    See also 'conjugacyclass' and 'conjtomin'.
    """
    if 'conjugacyclasses' in dir(W):
        return W.conjugacyclasses
    cl = []
    cent = []
    nam = []
    for t in W.cartantype:
        c = conjclassdata(t[0], len(t[1]))
        cl.append([[t[1][s] for s in w] for w in c['reps']])
        cent.append(c['centralisers'])
        nam.append(c['names'])
    ncl = []
    for w in cartesian(cl):
        nw = []
        for l in w:
            nw.extend(l)
        ncl.append(nw)
    ncent = []
    for cc in cartesian(cent):
        nc = 1
        for c in cc:
            nc *= c
        ncent.append(nc)
    nnam = [tuple(st) for st in cartesian(nam)]
    W.conjugacyclasses = {'reps': [w[:] for w in ncl], 'classnames': nnam[:],
                          'classlengths': [W.order // c for c in ncent]}
    return W.conjugacyclasses

# F identifyclasses


def identifyclasses(W, elms, minrep=False, verbose=False):
    """identifies the conjugacy classes to which the elements (given as
    reduced words)  in a list  belong.  If it is already known  that
    the elements  have  minimal length  in their  conjugacy classes,
    then the optional argument 'minrep' should be set to True.

    >>> W = coxeter("A",5)
    >>> identifyclasses(W,[W.permtoword(longestperm(W))])
    [3]
    >>> conjugacyclasses(W)['reps']
    [[],
     [0],
     [0, 2],
     [0, 2, 4],
     [0, 1],
     [0, 1, 3],
     [0, 1, 3, 4],
     [0, 1, 2],
     [0, 1, 2, 4],
     [0, 1, 2, 3],
     [0, 1, 2, 3, 4]]

    (Thus, the longest  element belongs  to the conjugacy class with
    respresentive [0,2,4].)

    See also 'fusionconjugacyclasses'.
    """
    clcl = coxeterclasses(W)
    clW = conjugacyclasses(W)['reps']
    invW = []
    for w in clW:
        fpw = ''
        bw = ''
        sw = set(w)
        for i in W.rank:
            if i in sw:
                bw += '1'
            else:
                bw += '0'
        fpw += 'c'
        fpw += str(clcl[bw]['class'])
        for o in W.rootorbits:
            fpw += 'o'
            fpw += str(len([1 for i in w if i in o]))
        invW.append(fpw)
    invH = []
    if minrep:
        elms1 = [conjtomin(W, W.wordtoperm(w)) for w in elms]
    else:
        elms1 = elms
    for w in elms1:
        fpw = ''
        bw = ''
        sw = set(w)
        for i in W.rank:
            if i in sw:
                bw += '1'
            else:
                bw += '0'
        fpw += 'c'
        fpw += str(clcl[bw]['class'])
        for o in W.rootorbits:
            fpw += 'o'
            fpw += str(len([1 for i in w if i in o]))
        invH.append(fpw)
    check = [invW.count(f) for f in invH]
    if set(check) == set([1]):
        fus = [invW.index(f) for f in invH]
    else:
        if verbose:
            print('🄸 using also traces ...')
        troubleH = [i for i in range(len(elms1)) if check[i] > 1]
        troublefp = [invH[i] for i in troubleH]
        troubleW = [i for i in range(len(clW)) if invW[i] in troublefp]
        matsH = []
        for i in troubleH:
            mm = W.wordtomat(elms1[i])
            matsH.append([list(l) for l in mm])
        matsW = []
        for i in troubleW:
            mm = W.wordtomat(clW[i])
            matsW.append([list(l) for l in mm])
        for i in range(len(troubleH)):
            spur = sum([matsH[i][j][j] for j in W.rank])
            if spur < 0:
                invH[troubleH[i]] += 'm'
                invH[troubleH[i]] += str(-spur)
            else:
                invH[troubleH[i]] += 'p'
                invH[troubleH[i]] += str(spur)
        for i in range(len(troubleW)):
            spur = sum([matsW[i][j][j] for j in W.rank])
            if spur < 0:
                invW[troubleW[i]] += 'm'
                invW[troubleW[i]] += str(-spur)
            else:
                invW[troubleW[i]] += 'p'
                invW[troubleW[i]] += str(spur)
        newcheck = [invW.count(f) for f in invH]
        if set(newcheck) == set([1]):
            print(' okay now\n')
            fus = [invW.index(f) for f in invH]
        else:
            print(' and characteristic polynomials \n')
            j = 0
            while j < len(W.rank) and set(newcheck) != set([1]):
                for i in range(len(troubleH)):
                    for k in W.rank:
                        matsH[i][k][k] += 1
                    dd = determinantmat(matsH[i])
                    if dd < 0:
                        invH[troubleH[i]] += 'm'
                        invH[troubleH[i]] += str(-dd)
                    else:
                        invH[troubleH[i]] += str(dd)
                for i in range(len(troubleW)):
                    for k in W.rank:
                        matsW[i][k][k] += 1
                    dd = determinantmat(matsW[i])
                    if dd < 0:
                        invW[troubleW[i]] += 'm'
                        invW[troubleW[i]] += str(-dd)
                    else:
                        invW[troubleW[i]] += str(dd)
                newcheck = [invW.count(f) for f in invH]
                j += 1
            if j <= len(W.rank):
                fus = [invW.index(f) for f in invH]
            else:
                print("mist!")
                return "mist"
    return fus


def fusionconjugacyclasses(H, W):
    """returns  the embedding of the conjugacy classes of a  reflection
    subgroup H into the whole group W. (See also 'identifyclasses'.)

    >>> W = coxeter("H",4)
    >>> H = reflectionsubgroup(W,[0,1,2]); print(H.cartantype)
    [['H', [0, 1, 2]]]
    >>> H.fusions
    {'H3c0c1c2': {'parabolic': True, 'subJ': [0, 1, 2]},
     'H4c0c1c2c3': {'parabolic': True, 'subJ': [0, 1, 2]}}
    >>> len(conjugacyclasses(W)['reps']); len(conjugacyclasses(H)['reps'])
    34
    10
    >>> f = fusionconjugacyclasses(H,W); f
    [0, 1, 2, 3, 4, 5, 9, 11, 15, 19]
    >>> f == identifyclasses(W,conjugacyclasses(H)['reps'],minrep=True)
    True
    >>> H.fusions
    {'H3c0c1c2': {'parabolic': True, 'subJ': [0, 1, 2]},
     'H4c0c1c2c3': {'classes': [0, 1, 2, 3, 4, 5, 9, 11, 15, 19],
      'parabolic': True,
      'subJ': [0, 1, 2]}}

    Now H.fusions has an additional entry containing the fusion
    of conjugacyclasses.

    >>> W = coxeter("B",6)
    >>> H = reflectionsubgroup(W,[1,2,3,4,5,11])
    >>> H.cartantype               # non-parabolic
    [['D', [0, 5, 1, 2, 3, 4]]]
    >>> fusionconjugacyclasses(H,W)
    [0, 2, 4, 6, 7, 10, 11, 14, 15, 17, 19, 21, 23, 25, 26, 26, 28, 30,
     33, 34, 37, 38, 41, 43, 44, 46, 48, 49, 52, 53, 55, 55, 58, 59, 62, 63, 63]
    """
    fh = H.fusions[W.cartanname]
    if 'classes' in fh:
        return fh['classes']
    ch = conjugacyclasses(H)
    if H.cartanname == W.cartanname:
        fh['classes'] = list(range(len(ch['reps'])))
        return fh['classes']
    if fh['parabolic']:
        clH = [[fh['subJ'][s] for s in w] for w in ch['reps']]
    else:
        clH = []
        for w in ch['reps']:
            nw = []
            for s in w:
                nw.extend(W.rootrepelms[fh['subJ'][s]])
                nw.append(W.rootorbits1[fh['subJ'][s]])
                nw.extend(W.rootrepelms[fh['subJ'][s]][::-1])
            clH.append(conjtomin(W, W.wordtoperm(nw)))
    H.fusions[W.cartanname]['classes'] = identifyclasses(W, clH, minrep=True)
    return H.fusions[W.cartanname]['classes']

# F Clifford form of elements in B_n


def cliffordB(W, w):
    """returns the  Clifford decomposition of an  element w in a
    Coxeter group of  type B_n,  as defined by Bonnafé-Iancu:

               w = a_w * a_l * sigma * b_w^(-1)

    where l is the t-length of w, a_l is the shortest element
    of W of  t-length l, sigma is an element of the parabolic
    subgroup  S_l x S_{n-l},  a_w, b_w are distinguished left
    coset representatives  with respect to this subgroup.

    The function returns the tuple [l,a_w,a_l,sigma,b_w].
    """
    lt = w.count(0)
    al = tuple(range(2 * W.N))
    for i in range(lt):
        for j in range(i):
            al = permmult(al, W.permgens[i - j])
        al = permmult(al, W.permgens[0])
    pw = W.wordtoperm(w)
    J1 = list(W.rank)[1:]
    H = reflectionsubgroup(W, J1)
    aw1 = redinrightcoset(W, H, perminverse(pw))
    aw = permmult(perminverse(aw1), al)
    sigma1 = permmult(aw1, pw)
    if 0 < lt < len(W.rank):
        J1.remove(lt)
    H1 = reflectionsubgroup(W, J1)
    bw = perminverse(redinrightcoset(W, H1, sigma1))
    sigma = permmult(sigma1, bw)
    if permmult(aw, permmult(al, permmult(sigma, perminverse(bw)))) != pw:
        print('Mist !!!')
        return False
    return [lt, aw, al, sigma, bw]
