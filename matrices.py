from functools import reduce

# F isprime


def isprime(n):
    if n == 0 or n == 1:
        return False
    if n < 0:
        return isprime(-n)
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True

# F nextprime


def nextprime(n):
    """returns the next prime number greater than a given integer.
    (Taken from the gap-library.)

    >>> nextprime(10**8)
    100000007
    >>> isprime(100000007)
    True

    See also 'isprime'.
    """
    if -3 == n:
        n = -2
    elif -3 < n < 2:
        n = 2
    elif n % 2 == 0:
        n += 1
    else:
        n += 2
    while not isprime(n):
        if n % 6 == 1:
            n += 4
        else:
            n += 2
    return n

# F intlcm


def intlcm(a, b):
    """returns the least common multiple of two integers.

    See also 'intlcmlist'.
    """
    gcd, tmp = a, b
    while tmp != 0:
        gcd, tmp = tmp, gcd % tmp
    return (a * b) // gcd


def intlcmlist(l):
    """returns the least common multiple of a list of integers.
    """
    return reduce(intlcm, l)

# F gcdex


def gcdex(m, n):
    """Extended gcd algorithm for integers (taken from the  gap-library). The
    function returns a dictionary with entries gcd, coeff1, coeff2, coeff3
    and coeff4. We have

        gcd = coeff1 * m + coeff2 * n  and  0 = coeff3 * m + coeff4 * n.

    >>> sorted(gcdex(4,15).items())
    [('coeff1', 4), ('coeff2', -1), ('coeff3', -15), ('coeff4', 4), ('gcd', 1)]

    (Thus, gcd(4,15)=1; we have 1=4*4+(-1)*15 and 0=(-15)*4+4*15.)
    """
    if 0 <= m:
        f, fm = m, 1
    else:
        f, fm = -m, -1
    if 0 <= n:
        g, gm = n, 0
    else:
        g, gm = -n, 0
    while g != 0:
        q, h, hm = f // g, g, gm
        g = f - q * g
        gm = fm - q * gm
        f, fm = h, hm
    if n == 0:
        return {'gcd': f, 'coeff1': fm, 'coeff2': 0, 'coeff3': gm, 'coeff4': 1}
    else:
        return {'gcd': f, 'coeff1': fm, 'coeff2': (f - fm * m) // n, 'coeff3': gm,
                'coeff4': (0 - gm * m) // n}


def idmat(rng, scalar):
    """returns the scalar matrix of size len(rng) with a given scalar
    on the diagonal.

    >>> idmat([0,1,2],-3)
    [[-3, 0, 0], [0, -3, 0], [0, 0, -3]]
    """
    m = [len(rng) * [0] for x in rng]
    for x in range(len(rng)):
        m[x][x] = scalar
    return m


def transposemat(mat):
    """returns the transpose of a matrix.

    >>> transposemat([[1,2,3],[4,5,6]])
    [[1, 4], [2, 5], [3, 6]]
    """
    return list(map(lambda *row: list(row), *mat))
#  return zip(*mat)

# F flatlist


def flatlist(lst):
    """returns the list of all elements that are contained in a given
    list or in any of its sublists. (Taken from the gap library.)

    >>> flatlist([1,[2,3],[[1,2],3]])
    [1, 2, 3, 1, 2, 3]
    >>> flatlist([]);
    []
    """
    flt = []
    for elm in lst:
        if not isinstance(elm, list):
            flt.append(elm)
        else:
            flt.extend(flatlist(elm))
    return flt

# F flatblockmat


def flatblockmat(blmat):
    """flattens a block matrix.
    """
    a = []
    for b in range(len(blmat)):
        for i in range(len(blmat[b][b])):
            a.append(flatlist(l[i] for l in blmat[b]))
    return a

# F transclos


def transclos(n, r):
    """returns the transitive closure of a relation on the integers
    0,1,...,n-1 given by a list of pairs in r.
    """
    m = []
    for i in range(n):
        l = n * [False]
        l[i] = True
        for p in r:
            if p[0] == i:
                l[p[1]] = True
        m.append(l)
    for i in range(n):
        for j in range(n):
            if m[j][i] == 1:
                m[j] = [m[i][k] or m[j][k] for k in range(n)]
    return m

# F noduplicates


def noduplicates(seq):
    """returns a new list in which all duplicates in the original list
    have been removed.  Also works for non-hashable types. (Learned
    this from stackoverflow.)

    >>> noduplicates([[1, 1], [2, 1], [1, 2], [1, 1], [3, 1]])
    [[1, 1], [2, 1], [1, 2], [3, 1]]
    """
    seen = set()
    return [x for x in seq if str(x) not in seen and not seen.add(str(x))]

# F partitioncap


def partitioncap(p1, p2):
    """returns the common refinement of two partitions of the same set.
    """
    s2 = [set([str(x) for x in l]) for l in p2]
    neu = []
    for p in p1:
        s = [str(x) for x in p]
        for j in range(len(s2)):
            nn = [p[i] for i in range(len(s)) if s[i] in s2[j]]
            if nn != []:
                neu.append(nn)
    return neu

# F permmult


def permmult(p, q):
    """returns the composition of two permutations (acting from the
    right.)
    """
    return tuple([q[i] for i in p])

# F printfunction


def printfunction(f):
    """prints the source code of a function.

    >>> printfunction(transposemat)
    def transposemat(mat):
      ...
      return list(map(lambda *row: list(row), *mat))
    """
    import inspect
    print(''.join(inspect.getsourcelines(f)[0]))

# F perminverse


def perminverse(p):
    """returns the inverse of a permutation.
    """
    np = len(p) * [0]
    for i in range(len(p)):
        np[p[i]] = i
    return tuple(np)

# F matadd


def matadd(a, b):
    """returns the sum of two matrices.
    """
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]

# F matsub


def matsub(a, b):
    """returns the difference of two matrices.
    """
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]

# F matmult


def matmult(a, b):
    """returns the matrix product of the matrices a and b.

    See also 'matadd' and 'scalmatmult'.
    """
    return [[sum(row[k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for row in a]

# F scalmatmult


def scalmatmult(a, b):
    """multiplies a matrix b with a scalar a.
    """
    return [[a * b[i][j] for j in range(len(b[0]))] for i in range(len(b))]

# F directsummat


def directsummat(a, b):
    """returns the matrix direct sum of the matrices a and b.

    >>> from coxeter import cartanmat
    >>> c = directsummat(cartanmat("A",2),cartanmat("G",2)); c
    [[2, -1, 0, 0], [-1, 2, 0, 0], [0, 0, 2, -1], [0, 0, -3, 2]]
    """
    if not a:
        return b
    if not b:
        return a
    c = idmat(range(len(a[0]) + len(b[0])), 0)
    for i in range(len(a[0])):
        for j in range(len(a[0])):
            c[i][j] = a[i][j]
    for i in range(len(b[0])):
        for j in range(len(b[0])):
            c[len(a[0]) + i][len(a[0]) + j] = b[i][j]
    return c


# F kroneckerproduct
def kroneckerproduct(mat1, mat2):
    """returns the  Kronecker product of the matrices mat1 and mat2. If
    mat1  has size m times n and mat2  has  size p times q, then the
    Kronecker product is a matrix of size m*p times n*q.

    >>> mat1=[[ 0,-1, 1],
    ...       [-2, 0,-2]]
    >>> mat2=[[1,1],
    ...       [0,1]]
    >>> kroneckerproduct(mat1,mat2)
    [[0, 0, -1, -1, 1, 1],
     [0, 0, 0, -1, 0, 1],
     [-2, -2, 0, 0, -2, -2],
     [0, -2, 0, 0, 0, -2]]

    (The program is taken from the gap library and re-written almost
    1-1 in python.)
    """
    krpr = []
    for row1 in mat1:
        for row2 in mat2:
            row = []
            for i in row1:
                row.extend([i * x for x in row2])
            krpr.append(row)
    return krpr

# F decomposemat


def decomposemat(mat):
    """tests if a matrix can be decomposed in block diagonal form; it
    is assumed that  mat[i][j]=0  if and only if  mat[j][i]=0. The
    result is range(len(mat[0]))  if  mat  can not be  decomposed.
    Otherwise, the lists of block indices are returned.

    >>> d=decomposemat([[ 2, 0,-1, 0, 0],
    ...                 [ 0, 2, 0,-3, 0],
    ...                 [-2, 0, 2, 0,-1],
    ...                 [ 0,-1, 0, 2, 0],
    ...                 [ 0, 0,-1, 0, 2]])
    >>> d
    [[0, 2, 4], [1, 3]]

    Thus, there are two blocks, obtained by taking the submatrices
    with row and column indices (0,2,4) and (1,3), respectively.
    """
    l = list(range(len(mat[0])))
    orbs = []
    while l != []:
        orb = [l[0]]
        for o in orb:
            for i in l:
                if mat[o][i] != 0 and i not in orb:
                    orb.append(i)
        for i in orb:
            l.remove(i)
        orb.sort()
        orbs.append(orb)
    return orbs

# F determinantmat1


def determinantmat1(mat):
    n = len(mat[0])
    if n == 1:
        return mat[0][0]
    else:
        d = 0
        for k in range(n):
            l = list(range(n))
            l.remove(k)
            if mat[k][0] != 0:
                d += (-1)**k * mat[k][0] * determinantmat1([[mat[i][j]
                                                           for j in range(1, n)] for i in l])
        return d

# F determinantmat


def determinantmat(mat):
    """returns the determinant of a matrix. If all coefficients are integers,
    the function uses a simplified version of the algorithm for  computing
    the elementary divisors of a matrix; in particular,  it does  not  use
    fractions. In general, it uses induction on the size of the matrix and
    expansion  along the first column.  (Thus,  it will  work for matrices
    of moderate size over any commutative ring).
    """
    a = [list(l) for l in mat]
    if not all(isinstance(x, int) for x in flatlist(a)):
        return determinantmat1(mat)
    n = len(mat[0])
    d = 1
    for p in range(n - 1):
        i = p
        while i < n and a[i][p] == 0:
            i += 1
        if i >= n:
            return 0
        if i != p:
            d = -d
            for j in range(n):
                x = a[p][j]
                a[p][j] = a[i][j]
                a[i][j] = x
        fertig = False
        i = p + 1
        while i < n and not fertig:
            if a[i][p] != 0:
                q = a[i][p] // a[p][p]
                for j in range(n):
                    a[i][j] -= q * a[p][j]
                if a[i][p] != 0:
                    for j in range(n):
                        x = a[p][j]
                        a[p][j] = a[i][j]
                        a[i][j] = x
                    d = -d
                else:
                    i += 1
            else:
                i += 1
        d *= a[p][p]
    d *= a[n - 1][n - 1]
    return d

# F inversematp


def inversematp(mat, p):
    """checks if an integer matrix is invertible; if this is the case, the
    function  returns the inverse of that matrix  modulo a prime number.
    """
    n = len(mat[0])
    a = []
    for i in range(n):
        l = [mat[i][j] % p for j in range(n)]
        l.extend(n * [0])
        l[n + i] = 1
        a.append(l)
    for k in range(n):
        k1 = k
        while k1 < n and a[k1][k] % p == 0:
            k1 += 1
        if k1 == n:
            return False
        if k != k1:
            for j in range(2 * n):
                a[k][j], a[k1][j] = a[k1][j], a[k][j]
        p1 = 1
        while (p1 * a[k][k]) % p != 1:
            p1 += 1
        for j in range(2 * n):
            a[k][j] = (p1 * a[k][j]) % p
        for i in range(n):
            if i != k:
                q = a[i][k]
                for j in range(2 * n):
                    a[i][j] = (a[i][j] - (q * a[k][j]) % p) % p
    return [l[n:] for l in a]

# F cartesian2


def cartesian2(liste, n, tup, i):
    if i == n:
        tups = [tup[:]]
    else:
        tups = []
        for l in liste[i]:
            if i == len(tup):
                tup.append(l)
            else:
                tup[i] = l
            tups.extend(cartesian2(liste, n, tup, i + 1))
    return tups

# F cartesian


def cartesian(*arg):
    """returns the cartesian product of lists.

    >>> cartesian([1,2],[3,4],[4,5])
    [[1, 3, 4], [1, 3, 5], [1, 4, 4], [1, 4, 5], [2, 3, 4], [2, 3, 5], [2, 4, 4], [2, 4, 5]]
    >>> cartesian([1,2,2],[1,1,2])
    [[1, 1], [1, 1], [1, 2], [2, 1], [2, 1], [2, 2], [2, 1], [2, 1], [2, 2]]

    In the first form the argument is a comma-separated sequence l1, l2,
    ..., and the function returns the cartesian product of l1, l2, ...

    In the second form the argument is a list of lists [l1,l2,,...], and
    and the function returns the cartesian product of those lists.

    If more than two lists are given,  cartesian(l1,l2,...) is the  same
    (up to some nested bracketing) as cartesian(cartesian(l1,l2),...).

    >>> cartesian(cartesian([1,2],[3,4]),[4,5])
    [[[1, 3], 4], [[1, 3], 5], [[1, 4], 4], [[1, 4], 5], [[2, 3], 4],
     [[2, 3], 5], [[2, 4], 4], [[2, 4], 5]]

    The ordering is exactly the same as in gap. (The program is actually
    taken from the gap library and re-written almost 1-1 in python.)
    """
    if len(arg) == 1:
        return cartesian2(arg[0], len(arg[0]), [], 0)
    else:
        return cartesian2(arg, len(arg), [], 0)

# F helppartitions


def helppartitions(n, m, part, i):
    if n == 0:
        part = part[:]
        parts = [part]
    elif n <= m:
        part = part[:]
        parts = [part]
        for l in range(2, n + 1):
            part[i] = l
            parts.extend(helppartitions(n - l, l, part, i + 1))
        for l in range(i, i + n):
            part[l] = 1
    else:
        part = part[:]
        parts = [part]
        for l in range(2, m + 1):
            part[i] = l
            parts.extend(helppartitions(n - l, l, part, i + 1))
        for l in range(i, i + n):
            part[l] = 1
    return parts

# F partitions


def partitions(n):
    """returns the list of all partitions of n.

    This should be an iterator.

    >>> partitions(5)
    [[1, 1, 1, 1, 1], [2, 1, 1, 1], [2, 2, 1], [3, 1, 1], [3, 2], [4, 1], [5]]

    The ordering is exactly the same as in gap. (The program is actually
    taken from the gap library and re-written almost 1-1 in python.)

    See also 'partitiontuples'.
    """
    return [[x for x in p if x > 0] for p in helppartitions(n, n, n * [0], 0)]

# F dualpartition


def dualpartition(mu):
    """returns the dual (or conjugate) partition to mu.
    """
    if not mu:
        return []
    return [len([1 for l in mu if l > j]) for j in range(mu[0])]

# F centraliser partition


def centraliserpartition(n, mu):
    """returns the order of the centraliser  of an element  of cycle
    type of a given partition in the  full symmetric group.  (The
    program is  taken from the  gap library and re-written almost
    1-1 in python.)
    """
    res, last, k = 1, 0, 1
    for p in mu:
        res *= p
        if p == last:
            k += 1
            res *= k
        else:
            k = 1
        last = p
    return res

# F differencepartitions


def differencepartitions(gamma, alpha):
    """returns  a dictionary with information about the  difference of
    two partitions (if it exists); this function is  needed for the
    computation of character values in type B_n. It is taken almost
    1-1 from the gap-chevie library.

    See also 'heckevalueB'.
    """
    dp = {'cc': 0, 'll': 0}
    if len(alpha) > len(gamma):
        return False
    old = []
    inhook = False
    alpha = alpha[:]
    for i in range(len(alpha), len(gamma)):
        alpha.append(0)
    for i in range(len(gamma)):
        if alpha[i] > gamma[i]:
            return False
        new = list(range(alpha[i], gamma[i]))
        intsec = [r for r in old if r in new]
        if len(intsec) > 1:
            return False
        elif len(intsec) == 1:
            dp['ll'] += 1
        else:
            if inhook:
                dp['cc'] += 1
                dp['d'] = old[0] - i
                inhook = False
        if new != []:
            inhook = True
        old = new
    if inhook:
        dp['cc'] += 1
        dp['d'] = old[0] - len(gamma)
    return dp

# F bipartitions


def bipartitions(n):
    """returns the list of all bipartitions of n (as in gap). The
    ordering is different from that of partitiontuples(n,2).
    """
    if n == 0:
        return [[[], []]]
    pm = [[] for i in range(n)]
    for m in range(1, n + 1):
        pm[m - 1].append([[], [m]])
        for k in range(m + 1, n + 1):
            for t in pm[k - m - 1]:
                s = [[], [m]]
                s[1].extend(t[1])
                pm[k - 1].append(s)
    for m in range(1, n // 2 + 1):
        pm[m - 1].append([[m], []])
        for k in range(m + 1, n - m + 1):
            for t in pm[k - m - 1]:
                s = [[m], t[1]]
                s[0].extend(t[0])
                pm[k - 1].append(s)
    res = []
    for k in range(1, n):
        for t in pm[n - k - 1]:
            s = [[k], t[1]]
            s[0].extend(t[0])
            res.append(s)
    res.append([[n], []])
    res.extend(pm[n - 1])
    return res

# F partitiontuples


def partitiontuples(n, r):
    """returns the list of all r-tuples of partitions of n.

    This should be an iterator.

    >>> partitiontuples(3,2)
    [[[1, 1, 1], []],
     [[1, 1], [1]],
     [[1], [1, 1]],
     [[], [1, 1, 1]],
     [[2, 1], []],
     [[1], [2]],
     [[2], [1]],
     [[], [2, 1]],
     [[3], []],
     [[], [3]]]

    The ordering is exactly the same as in gap. (The program is actually
    taken from the gap library and re-written almost 1-1 in python.)

    See also 'partitions'.
    """
    empty = {'tup': [[] for x in range(r)], 'pos': (n - 1) * [1]}
    if n == 0:
        return [empty['tup']]
    pm = [[] for x in range(1, n)]
    for m in range(1, n // 2 + 1):
        for i in range(1, r + 1):
            s = {'tup': [l[:] for l in empty['tup']], 'pos': empty['pos'][:]}
            s['tup'][i - 1] = [m]
            s['pos'][m - 1] = i
            pm[m - 1].append(s)
        for k in range(m + 1, n - m + 1):
            for t in pm[k - m - 1]:
                for i in range(t['pos'][m - 1], r + 1):
                    t1 = {'tup': [l[:] for l in t['tup']], 'pos': t['pos'][:]}
                    s = [m]
                    s.extend(t['tup'][i - 1])
                    t1['tup'][i - 1] = s
                    t1['pos'][m - 1] = i
                    pm[k - 1].append(t1)
    res = []
    for k in range(1, n):
        for t in pm[n - k - 1]:
            for i in range(t['pos'][k - 1], r + 1):
                t1 = [l[:] for l in t['tup']]
                s = [k]
                s.extend(t['tup'][i - 1])
                t1[i - 1] = s
                res.append(t1)
    for i in range(1, r + 1):
        s = [l[:] for l in empty['tup']]
        s[i - 1] = [n]
        res.append(s)
    return res

# F centralisertuple


def centralisertuple(n, r, mu):
    """returns the order of the centraliser of an element of a given
    type (specified by an r-tuple of partitions mu) in the wreath
    product of a cyclic group of order r with the full  symmetric
    group of degree n. (The program is taken from the gap library
    and re-written almost 1-1 in python.)
    """
    res = 1
    for i in range(r):
        last, k = 0, 1
        for p in mu[i]:
            res *= r * p
            if p == last:
                k += 1
                res *= k
            else:
                k = 1
            last = p
    return res

# F lusztigsymbolB


def lusztigsymbolB(n, vs, vt, dblpart):
    """returns the symbol associated with a  bipartition, as defined
    by Lusztig,  taking into account  weights.  In this form, the
    total number of entries in a symbol only depends on n and the
    parameters (but not on the bipartition).

    >>> bipartitions(2)
    [[[1], [1]], [[1, 1], []], [[2], []], [[], [1, 1]], [[], [2]]]
    >>> [lusztigsymbolB(2,1,1,pi) for pi in bipartitions(2)]
    [[[0, 1, 3], [0, 2]],
     [[0, 2, 3], [0, 1]],
     [[0, 1, 4], [0, 1]],
     [[0, 1, 2], [1, 2]],
     [[0, 1, 2], [0, 3]]]

    See also 'redlusztigsymbolB'.
    """
    q, r = vt // vs, vt % vs
    a, b = dblpart[0][:], dblpart[1][:]
    if len(a) > len(b) + q:
        b.extend((len(a) - len(b) - q) * [0])
    elif len(b) + q > len(a):
        a.extend((len(b) - len(a) + q) * [0])
    while len(a) + len(b) < 2 * n + q:
        a.append(0)
        b.append(0)
    la, mu = (n + q) * [0], n * [0]
    for i in range(1, len(b) + 1):
        la[i - 1] = vs * (a[len(a) - i] + i - 1) + r
        mu[i - 1] = vs * (b[len(b) - i] + i - 1)
    for i in range(len(b) + 1, len(a) + 1):
        la[i - 1] = vs * (a[len(a) - i] + i - 1) + r
    return [la, mu]

# F redlusztigsymbolB


def redlusztigsymbolB(vs, vt, dblpart):
    """similar to 'lusztigsymbolB' but now the number of entries in a
    symbol is as small as possible (depending on the bipartition).

    >>> bipartitions(2)
    [[[1], [1]], [[1, 1], []], [[2], []], [[], [1, 1]], [[], [2]]]
    >>> [redlusztigsymbolB(1,1,pi) for pi in bipartitions(2)]
    [[[0, 2], [1]],
     [[1, 2], [0]],
     [[2], []],
     [[0, 1, 2],
     [1, 2]], [[0, 1], [2]]]

    See also 'lusztigsymbolB'.
    """
    q, r = vt // vs, vt % vs
    a, b = dblpart[0][:], dblpart[1][:]
    if len(a) > len(b) + q:
        b.extend((len(a) - len(b) - q) * [0])
    elif len(b) + q > len(a):
        a.extend((len(b) - len(a) + q) * [0])
    n = (len(a) + len(b) - q) // 2
    la, mu = (n + q) * [0], n * [0]
    for i in range(1, len(b) + 1):
        la[i - 1] = vs * (a[len(a) - i] + i - 1) + r
        mu[i - 1] = vs * (b[len(b) - i] + i - 1)
    for i in range(len(b) + 1, len(a) + 1):
        la[i - 1] = vs * (a[len(a) - i] + i - 1) + r
    return [la, mu]

# F ainvbipartition


def ainvbipartition(n, vs, vt, bip):
    """returns the a-invariant of a  bipartition,  computed from
    the associated Lusztig symbol. See also 'lusztigsymbolB'.
    """
    q, r = vt // vs, vt % vs
    p = []
    s = lusztigsymbolB(n, vs, vt, bip)
    for i in s[0]:
        p.append(i)
    for i in s[1]:
        p.append(i)
    p.sort()
    N = (len(p) - q) // 2
    z0 = [i * vs for i in range(N)]
    z0.extend([i * vs + r for i in range(N + q)])
    z0.sort()
    return sum(i * (p[-i - 1] - z0[-i - 1]) for i in range(len(p)))

# F displaymat


def displaymat(mat, rows=None, cols=None, width=78):
    """displays a matrix, where the optional arguments 'rows' and 'cols'
    can be used to specify labels for the rows and columns.  There is
    a further  optional  argument by which one can set the 'width' of
    the display, i.e., the maximum number of characters printed  (the
    default value is 78 characters per line).

    >>> from coxeter import coxeter
    >>> from pycox import chartable
    >>> displaymat(chartable(coxeter("H",3))['irreducibles'])
     1 -1     1  1  1     -1     1 -1     -1 -1
     1  1     1  1  1      1     1  1      1  1
     5 -1     .  1 -1      .     .  1      . -5
     5  1     .  1 -1      .     . -1      .  5
     3 -1   ir5 -1  .  1-ir5 1-ir5  .    ir5  3
     3 -1 1-ir5 -1  .    ir5   ir5  .  1-ir5  3
     3  1   ir5 -1  . -1+ir5 1-ir5  .   -ir5 -3
     3  1 1-ir5 -1  .   -ir5   ir5  . -1+ir5 -3
     4  .    -1  .  1      1    -1 -1      1 -4
     4  .    -1  .  1     -1    -1  1     -1  4

    (Values equal to 0 are printed as '.'.)

    >>> displaymat([[1,2],[3,4]],['A','B'],['C','D'], width=10)
    ──────────
      C D
    ──────────
    A 1 2
    B 3 4

    See also 'displaychartable'.
    """
    m = len(mat)
    n = len(mat[0])
    csp = [max(len(repr(mat[i][j])) for i in range(m)) for j in range(n)]
    if cols is not None:
        csp = [max(len(str(cols[j])), csp[j]) + 1 for j in range(n)]
    else:
        csp = [csp[j] + 1 for j in range(n)]
    if rows is not None:
        maxr = max(len(str(r)) for r in rows)
    else:
        maxr = 0
    co = 0
    cut = [0]
    for j in range(len(csp)):
        if co + csp[j] <= width - maxr:
            co += csp[j]
        else:
            cut.append(j)
            co = csp[j]
    if cut[:-1] != n:
        cut.append(n)
    for k in range(len(cut) - 1):
        if cols is not None:
            print(width * '─')
            print(maxr * ' ', end="")
            for j in range(cut[k], cut[k + 1]):
                print((csp[j] - len(str(cols[j]))) * ' ' + str(cols[j]), end="")
            print()
            print(width * '─')
        for i in range(m):
            if rows is not None:
                print((maxr - len(str(rows[i]))) * ' ' + str(rows[i]), end="")
            for j in range(cut[k], cut[k + 1]):
                if mat[i][j] == 0:
                    print((csp[j] - len(repr(mat[i][j]))) * ' ' + '.', end="")
                elif isinstance(mat[i][j], int):
                    print((csp[j] - len(repr(mat[i][j]))) * ' ' + str(mat[i][j]), end="")
                else:
                    print((csp[j] - len(repr(mat[i][j]))) * ' ' + repr(mat[i][j]), end="")
            print()
    return None
