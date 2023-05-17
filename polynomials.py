from math import cos, sin, pi


# F class-lpol: basic support for Laurent polynomials in one variable
class lpol:
    """creates a Laurent polynomial in one variable, from a list of
    coefficients, a valuation and a name. The result is a python
    class with components:

       coeffs     list of coefficients
       valuation  order of the pole at 0
       degree     degree of the polynomial
       vname      name for the variable
       vcyc       see the help of 'cycldec' for explanation

    The usual  operations  (addition,  multiplication, ...)  are
    defined.  If, in the course  of performing such operations a
    Laurent polynomial reduces to 0, then only 0 (as an integer)
    will be returned.

    The coefficients can be taken from any commutative ring that
    is available; for example, they  could  again be polynomials
    (in a different variable).

    >>> v=lpol([1],1,'v')    # creates the indeterminate v
    >>> (v+1)**2-v**2-2*v-1
    0
    >>> p=(2*v-1)**3*v**(-2); p
    -v**(-2)+6*v**(-1)-12+8*v
    >>> print(p)
    lpol([-1, 6, -12, 8],-2,'v')
    >>> p.degree
    1
    >>> p.val
    -2
    >>> p.value(-1)
    -27

    >>> u=lpol([1],1,'u')   # create another indeterminate
    >>> lpol([u**2+2,-3,u**(-1)],-17,'v')
    (2+u**2)*v**(-17)-3*v**(-16)+(u**(-1))*v**(-15)
    >>> u+v
    # Warning: different variables !
    False
    >>> u*v**0+v     # force u to be treated as constant polynomial in v
    (u)+v

    See also 'interpolatepol'
    """

    def __init__(self, coeffs, val, vname):
        self.vname = vname
        self.vcyc = False
        if all(c == 0 for c in coeffs):
            self.coeffs = []
            self.val = 0
            self.degree = 0
        else:
            a, e = 0, len(coeffs)
            while coeffs[a] == 0:
                a += 1
            while coeffs[e - 1] == 0:
                e -= 1
            self.coeffs = coeffs[a:e]
            self.val = val + a
            self.degree = val + e - 1

    def __repr__(self):
        if not self.coeffs:
            return '0'
        r = ''
        for i in range(len(self.coeffs)):
            if self.coeffs[i] != 0:
                if r and not (type(self.coeffs[i]) == type(0) and self.coeffs[i] < 0):
                    r += '+'
                if i + self.val == 0:
                    if type(self.coeffs[i]) == type(0):
                        r += repr(self.coeffs[i])
                    else:
                        r += '(' + repr(self.coeffs[i]) + ')'
                else:
                    if self.coeffs[i] == -1:
                        r += '-' + self.vname
                    elif self.coeffs[i] == 1:
                        r += self.vname
                    else:
                        if type(self.coeffs[i]) == type(0):
                            r += repr(self.coeffs[i]) + '*' + self.vname
                        else:
                            r += '(' + repr(self.coeffs[i]) + ')*' + self.vname
                if i + self.val < 0:
                    r += '**(' + str(i + self.val) + ')'
                if i + self.val > 1:
                    r += '**' + str(i + self.val)
        return r

    def __str__(self):
        return 'lpol(' + str(self.coeffs) + ',' + str(self.val) + ",'" + str(self.vname) + "')"

    def value(self, x):
        """evaluates a polynomial.
        """
        if not self.coeffs:
            return 0
        y = 0
        for i in range(len(self.coeffs)):
            y = x * y + self.coeffs[-i - 1]
        if self.val < 0 and x in [-1, 1]:
            return y * x**(-self.val)
        else:
            return y * x**self.val

    def __neg__(self):
        return lpol([-c for c in self.coeffs], self.val, self.vname)

    def __eq__(self, f):
        if self.coeffs == []:
            return f == 0
        elif type(self) == type(f) and self.__class__ == f.__class__:
            return self.coeffs == f.coeffs and self.val == f.val and self.vname == f.vname
        elif type(f) == type(self.coeffs[0]):
            return len(self.coeffs) == 1 and self.val == 0 and self.coeffs[0] == f
        else:
            return False

    def __ne__(self, f):
        return not self == f

    def __radd__(self, scal):  # scalar addition on left
        if scal == 0:
            return self
        if self.coeffs == []:
            return scal
        f = self.coeffs[:]
        if self.val < 0:
            if len(self.coeffs) + self.val <= 0:
                f += (-len(self.coeffs) - self.val) * [0]
                f.append(scal)
            else:
                f[-self.val] += scal
            return lpol(f, self.val, self.vname)
        elif self.val == 0:
            f[0] += scal
            return lpol(f, self.val, self.vname)
        else:
            f = self.val * [0] + f
            f[0] = scal
            return lpol(f, 0, self.vname)

    def __add__(self, f):
        if type(f) != type(self):
            return f + self
        if self.__class__ == f.__class__ and self.vname != f.vname:
            print("# Warning: different variables !")
            return False
        if f.val <= self.val:
            ng = (self.val - f.val) * [0] + self.coeffs
            if len(f.coeffs) > len(ng):
                ng.extend((len(f.coeffs) - len(ng)) * [0])
            for i in range(len(f.coeffs)):
                ng[i] += f.coeffs[i]
            if all(c == 0 for c in ng):
                return 0
            else:
                return lpol(ng, f.val, self.vname)
        else:
            nf = (f.val - self.val) * [0] + f.coeffs
            if len(self.coeffs) > len(nf):
                nf.extend((len(self.coeffs) - len(nf)) * [0])
            for i in range(len(self.coeffs)):
                nf[i] += self.coeffs[i]
            if all(c == 0 for c in nf):
                return 0
            else:
                return lpol(nf, self.val, self.vname)

    def __rmul__(self, scal):      # scalar multiplication from the left
        if scal == 0:
            # return 0
            return lpol([0], 0, self.vname)
        else:
            return lpol([scal * c for c in self.coeffs], self.val, self.vname)

    def __mul__(self, f):
        if type(self) == type(f) and self.__class__ == f.__class__:
            if self.vname == f.vname:
                m = len(self.coeffs) + len(f.coeffs) - 1
                return lpol([sum(self.coeffs[i] * f.coeffs[k - i] for i in range(m)
                                 if i < len(self.coeffs) and 0 <= k - i < len(f.coeffs))
                             for k in range(m)], self.val + f.val, self.vname)
            else:
                return lpol([self * c for c in f.coeffs], f.val, f.vname)
        else:
            if f == 0:
                return 0
            else:
                return lpol([c * f for c in self.coeffs], self.val, self.vname)

    def __sub__(self, f):
        return self + (-f)

    def __rsub__(self, f):           # subtract polynomial from a scalar
        return f + (-self)

    def __pow__(self, n):
        if n == 0:
            return lpol([1], 0, self.vname)
        elif n == 1:
            return self
        elif len(self.coeffs) == 1 and self.coeffs[0] in [-1, 1]:
            if n % 2 == 0:
                return lpol([1], n * self.val, self.vname)
            else:
                return lpol([self.coeffs[0]], n * self.val, self.vname)
        else:
            x = 1
            for i in range(n):
                x *= self
            return x

    def __divmod__(self, g):
        """divides f (=self)  by g leaving remainder; here, all coefficients
        of f must be divisible by  the coefficient  of the highest power
        of the variable in g.

        Assuming that f,g are Laurent polynomials in v, the function first
        expresses f and g in the form

           f = v**f.val * nf    and   g = v**g.val * ng

        where nf, ng are genuine polynomials in v  with non-zero  constant
        terms. Then the function finds the expression nf=q*ng+r where q, r
        are polynomials such that r=0 or degree(r)<degree(ng). This yields

          f = v**(f.val-g.val) * q * g + v**f.val * r.

        The function returns the tuple (v**(f.val-g.val)*q,v**f.val*r).

        >>> v=lpol([1],1,"v")
        >>> divmod(v**2+2,-v**3*(v+v**(-1)))
        (-v**(-2), 1)

        In some cases this may lead to unexpected results:
        >>> divmod(2*v,v+1)
        (0, 2*v)
        """
        v = lpol([1], 1, self.vname)
        r = v**(-self.val) * self
        # if type(g)==type(self.coeffs[0]) or type(g)==type(int(self.coeffs[0]))\
        #     or (type(self.coeffs[0])==type(10000000000) and type(g)==type(0)):
        if type(g) == type(0):
            if all(c % g == 0 for c in r.coeffs):
                return (lpol([c // g for c in self.coeffs], self.val, self.vname), 0)
            else:
                return False
        ng = v**(-g.val) * g
        if not all(c % ng.coeffs[-1] == 0 for c in r.coeffs):
            return False
        quot = 0
        while type(r) == type(ng) and r.degree >= ng.degree:
            q = (r.coeffs[-1] // ng.coeffs[-1]) * v**(r.degree - ng.degree)
            r -= q * ng
            quot += q
        # if not self==v**(self.val-g.val)*quot*g+v**self.val*r:
        #  print("mist")
        #  return "mist"
        return (v**(self.val - g.val) * quot, v**self.val * r)

    def __rfloordiv__(self, f):
        if f == 1:
            return self**(-1)
        else:
            return False
# end of definition of class lpol


def evalpol(f, x):
    if type(f) == type(0):
        return f
    else:
        return f.value(x)


v = lpol([1], 1, "v")    # polynomial v

# F cyclpol


def cyclpol(n, u):
    """returns the n-th cyclotomic polynomial in the variable u.
    """
    if n == 1:
        return u - 1
    m = n // 2
    while n % m != 0:
        m -= 1
    f = divmod(u**n - 1, u**m - 1)[0]
    for d in range(1, n):
        if n % d == 0 and m % d != 0:
            f = divmod(f, cyclpol(d, u))[0]
    return f

# F cyclpol5


def cyclpol5(u):
    """returns those cyclotomic polynomials over the number field
    generated by (1+sqrt(5))/2 which are  relevant for Coxeter
    groups of type H_3 and H_4.
    """
    ir5 = ir(5)
    return {'5a': u**2 + ir5 * u + 1, '5b': u**2 + (1 - ir5) * u + 1, '10a': u**2 - ir5 * u + 1,
            '10b': u**2 + (ir5 - 1) * u + 1, '15a': u**4 - ir5 * u**3 + ir5 * u**2 - ir5 * u + 1,
            '15b': u**4 + (ir5 - 1) * u**3 + (1 - ir5) * u**2 + (ir5 - 1) * u + 1,
            '20a': u**4 - ir5 * u**2 + 1, '20b': u**4 + (ir5 - 1) * u**2 + 1,
            '30a': u**4 + ir5 * u**3 + ir5 * u**2 + ir5 * u + 1,
            '30b': u**4 + (1 - ir5) * u**3 + (1 - ir5) * u**2 + (1 - ir5) * u + 1}

# F class-lpolmod: truncated polynomials


class lpolmod:
    """creates a polynomial in one variable with integer coefficients,
    similar to 'lpol'  but where  all arithmetic is  done  modulo a
    given monic polynomial.  The  resulting  python  class  has the
    following components:

       coeffs     list of coefficients
       val        order of the pole at 0
       degree     degree of the polynomial
       phi        monic polynomial
       zname      name for the class of the variable

    In particular, by working modulo a cyclotomic polynomial,  this
    provides an arithmetic for cyclotomic integers.

    See also 'rootof1'.
    """

    def __init__(self, coeffs, val, mpol, zname):
        self.zname = zname
        self.phi = mpol
        if all(c == 0 for c in coeffs):
            self.coeffs = []
            self.val = 0
            self.degree = 0
            self.phi = mpol
            self.truncated = True
        else:
            a, e = 0, len(coeffs)
            while coeffs[a] == 0:
                a += 1
            while coeffs[e - 1] == 0:
                e -= 1
            self.coeffs = coeffs[a:e]
            self.val = val + a
            self.degree = val + e - 1
            self.truncated = False

    def __repr__(self):
        if self.coeffs == []:
            return '0'
        r = ''
        for i in range(len(self.coeffs)):
            if self.coeffs[i] != 0:
                if r != '' and not (type(self.coeffs[i]) == type(0) and self.coeffs[i] < 0):
                    r += '+'
                if i + self.val == 0:
                    if type(self.coeffs[i]) == type(0):
                        r += repr(self.coeffs[i])
                    else:
                        r += '(' + repr(self.coeffs[i]) + ')'
                else:
                    if self.coeffs[i] == -1:
                        r += '-' + self.zname
                    elif self.coeffs[i] == 1:
                        r += self.zname
                    else:
                        if type(self.coeffs[i]) == type(0):
                            r += repr(self.coeffs[i]) + '*' + self.zname
                        else:
                            r += '(' + repr(self.coeffs[i]) + ')*' + self.zname
                if i + self.val < 0:
                    r += '**(' + str(i + self.val) + ')'
                if i + self.val > 1:
                    r += '**' + str(i + self.val)
        return r

    def __str__(self):
        r = 'lpolmod(' + str(self.coeffs) + ',' + str(self.val) + ",'" + str(self.zname) + "')"
        return r

    def truncate(self):
        if self.truncated:
            return self
        else:
            v = lpol([1], 1, self.phi.vname)
            r = lpol(self.coeffs, self.val, self.phi.vname)
            while type(r) == type(v) and r.degree >= self.phi.degree:
                r -= r.coeffs[-1] * v**(r.degree - self.phi.degree) * self.phi
            if type(r) == type(0):
                return r
            elif r.coeffs == []:
                return 0
            elif r.val == 0 and len(r.coeffs) == 1:
                return r.coeffs[0]
            else:
                return lpolmod(r.coeffs, r.val, self.phi, self.zname)

    def value(self, x):
        """evaluates a truncated polynomial.
        """
        if self.coeffs == []:
            return 0
        y = 0
        for i in range(len(self.coeffs)):
            y = x * y + self.coeffs[-i - 1]
        if self.val < 0 and x in [-1, 1]:
            return y * x**(-self.val)
        else:
            return y * x**self.val

    def __eq__(self, f):
        if type(f) == type(0):
            if self.coeffs == []:
                return f == 0
            else:
                return self.val == 0 and len(self.coeffs) == 1 and self.coeffs[0] == f
        else:
            if type(self) == type(f) and 'zname' in dir(f) and self.zname == f.zname:
                return self.coeffs == f.coeffs and self.val == f.val and self.phi == f.phi
            else:
                return False

    def __ne__(self, f):
        return not self == f

    def __gt__(self, f):
        z = self - f
        if type(z) == type(0):
            return z > 0
        elif z.zname[0] == 'E':
            n = int(z.zname[2:-1])
            z1 = z.value(rootof1(n)**-1)
            if z == z1:
                rz = z.value(cos(2 * pi / n) + sin(2 * pi / n) * 1j).real
                return rz > 0
            else:
                return False
        else:
            return False

    def __lt__(self, f):
        z = f - self
        if type(z) == type(0):
            return z > 0
        elif z.zname[0] == 'E':
            n = int(z.zname[2:-1])
            z1 = z.value(rootof1(n)**-1)
            if z == z1:
                rz = z.value(cos(2 * pi / n) + sin(2 * pi / n) * 1j).real
                return rz > 0
            else:
                return False
        else:
            return False

    def __ge__(self, f):
        return self == f or self > f

    def __le__(self, f):
        return self == f or self < f

    def __neg__(self):
        return lpolmod([-c for c in self.coeffs], self.val, self.phi, self.zname)

    def __add__(self, f):
        x = lpol(self.coeffs, self.val, self.phi.vname)
        if type(f) == type(0):
            r = x + lpol([f], 0, self.phi.vname)
            if r == 0:
                return 0
            else:
                return lpolmod(r.coeffs, r.val, self.phi, self.zname).truncate()
        elif type(f) == type(self) and 'zname' in dir(f) and f.zname == self.zname:
            r = x + lpol(f.coeffs, f.val, self.phi.vname)
            if r == 0:
                return 0
            else:
                return lpolmod(r.coeffs, r.val, self.phi, self.zname).truncate()
        else:
            return False

    def __radd__(self, scal):  # scalar addition on left
        return self + scal

    def __sub__(self, f):
        return self + (-f)

    def __rsub__(self, f):           # subtract polynomial from a scalar
        return f + (-self)

    def __mul__(self, f):
        x = lpol(self.coeffs, self.val, self.phi.vname)
        if type(f) == type(0):
            r = x * lpol([f], 0, self.phi.vname)
            if r == 0:
                return 0
            else:
                return lpolmod(r.coeffs, r.val, self.phi, self.zname).truncate()
        elif type(f) == type(self):
            if 'zname' in dir(f) and f.zname == self.zname:
                r = x * lpol(f.coeffs, f.val, self.phi.vname)
                if r == 0:
                    return 0
                else:
                    return lpolmod(r.coeffs, r.val, self.phi, self.zname).truncate()
            else:
                return f * self
        else:
            return f * self

    def __rmul__(self, scal):      # scalar multiplication from the left
        if scal == 0:
            return 0
        else:
            return lpolmod([scal * c for c in self.coeffs], self.val,
                           self.phi, self.zname).truncate()

    def __pow__(self, n):
        if n == 0:
            return lpolmod([1], 0, self.phi, self.zname)
        elif n == 1:
            return self
        elif n < 0 and len(self.coeffs) == 1 and self.coeffs[0] == 1:
            cf = self.phi.coeffs
            if self.phi.val > 0 or (cf[0] != 1 and cf[0] != -1):
                return False
            else:
                return (lpolmod([-cf[0] * i for i in cf[1:]], 0, self.phi,
                                self.zname).truncate())**(-n)
        elif len(self.coeffs) == 1 and self.coeffs[0] in [-1, 1]:
            if n % 2 == 0:
                return lpolmod([1], n * self.val, self.phi, self.zname).truncate()
            else:
                return lpolmod([self.coeffs[0]], n * self.val, self.phi,
                               self.zname).truncate()
        else:
            x = 1
            for i in range(n):
                x *= self
            return x

    def __mod__(self, d):
        """(Only works if d is an integer.)
        """
        if type(d) == type(0):
            g = d
        elif type(d) == type(self) and d.val == 0 and d.degree == 0:
            g = d.coeffs[0]
        else:
            return False
        return lpolmod([c % g for c in self.coeffs],
                       self.val, self.phi, self.zname).truncate()

    def __floordiv__(self, d):
        """(Only works if d is an integer.)
        """
        if type(d) == type(0):
            g = d
        elif type(d) == type(self) and d.val == 0 and d.degree == 0:
            g = d.coeffs[0]
        else:
            return False
        if all(c % g == 0 for c in self.coeffs):
            return lpolmod([c // g for c in self.coeffs],
                           self.val, self.phi, self.zname)
        else:
            return False

    def __divmod__(self, f):
        return (self // f, self % f)

    def __rfloordiv__(self, f):
        if f == 1:
            return self**(-1)
        else:
            return False
# end of definition of class lpolmod


def rootof1(n):
    """creates a primitive root of unity. Internally, this is done
    by  using the 'lpolmod' function. It is not very efficient;
    the  main reason why we have it here is  because of its use
    for dihedral groups I_2(m) where m>6.

    >>> z=rootof1(4)
    >>> z**2
    -1
    >>> from chv1r6180 import cartanmat, coxeter
    >>> A = cartanmat("I8",2); A
    [[2, -1], [-2-E(8)+E(8)**3, 2]]

    Here E(8) is the default name (as in GAP)

    >>> W = coxeter(A); W.cartantype
    [['I8', [0, 1]]]
    >>> a=rootof1(8); x=a-a**3; x
    E(8)-E(8)**3
    >>> x>0
    True
    >>> x**2
    2

    (Thus, x is the positive square root of 2.)

    See also 'lpolmod' and 'zeta5'.
    """
    return lpolmod([1], 1, cyclpol(n, lpol([1], 1, 'unity' + str(n))), 'E(' + str(n) + ')')


def E(n):
    return rootof1(n)


def ir(m):
    from zeta5 import zeta5
    if m == 2:
        return 0
    elif m == 3:
        return 1
    elif m == 5:
        return zeta5(0, 1)
    else:
        return (rootof1(2 * m) + rootof1(2 * m)**-1).truncate()


ir5 = ir(5)

# F cycldec


def cycldec(pol, maxe=1000):
    """checks if a polynomial is a product of  cyclotomic polynomials,
    up to a constant and a power of the  indeterminate.  If this is
    the case, the function returns a triple (c,n,l)  where c is the
    constant, n is  the exponent of the  indeterminate, and  l is a
    list of pairs (e_i,m_i) such that

       pol = c * u^n * prod_i Phi_{e_i}(u)^{m_i};

    here, Phi_e denotes the e-th cyclomotic polynomial. This triple
    will then be assigned to the vcyc component of pol.  If no such
    product decomposition exists, the function returns 'False'.  By
    default,  the function  only tries the polynomials Phi_e  where
    e<=1000. One can increase  this  bound by setting the  optional
    argument 'maxe' to a higher value.

    For  example, all  the Schur elements of  generic Iwahori-Hecke
    algebras admit such a decomposition.

    >>> from chv1r6180 import poincarepol, coxeter
    >>> p = poincarepol(coxeter("F",4),v); p
    1+4*v+9*v**2+16*v**3+25*v**4+36*v**5+48*v**6+60*v**7+71*v**8+80*v**9+87*v**10+92*v**11+94*v**12+92*v**13+87*v**14+80*v**15+71*v**16+60*v**17+48*v**18+36*v**19+25*v**20+16*v**21+9*v**22+4*v**23+v**24
    >>> p.vcyc
    False
    >>> cycldec(p)
    [1, 0, [[2, 4], [3, 2], [4, 2], [6, 2], [8, 1], [12, 1]]]
    >>> p.vcyc
    [1, 0, [[2, 4], [3, 2], [4, 2], [6, 2], [8, 1], [12, 1]]]

    See also 'lcmcyclpol'.
    """
    u = lpol([1], 1, pol.vname)
    np = u**(-pol.val) * pol
    li = []
    e = 1
    phi = u - 1
    while np.degree > 0 and e <= maxe:
        q, r = divmod(np, phi)
        m = 0
        while r == 0:
            np = lpol(q.coeffs, q.val, q.vname)
            m += 1
            q, r = divmod(q, phi)
        if m > 0:
            li.append([e, m])
        e += 1
        phi = cyclpol(e, u)
    if np.degree == 0:
        pol.vcyc = [np.coeffs[0], pol.val, li[:]]
        return pol.vcyc
    else:
        return False

# F lcmcyclpol


def lcmcyclpol(pols):
    """returns the least common multiple of a list of polynomials which
    have a decomposition as returned by 'cycldec'.
    """
    from matrices import intlcm
    if len(pols) == 1:
        return pols[0]
    q = lpol([1], 1, pols[0].vname)
    ds = [cycldec(p) for p in pols]
    res = (max([c[2][-1][0] for c in ds]) + 1) * [0]
    res[0] = 1
    for c in ds:
        res[0] = intlcm(res[0], c[0])
        for m in c[2]:
            if m[1] > res[m[0]]:
                res[m[0]] = m[1]
    p = res[0]
    for i in range(1, len(res)):
        if res[i] > 0:
            p *= cyclpol(i, q)**res[i]
    return p

# F interpolate polynomial


def interpolatepol(v, x, y):
    """returns the unique polynomial in  v of degree less than n  which has
    value y[i] at x[i] for all i=0,...n-1. (Taken from the gap-library).

    >>> v=lpol([1],1,"v")
    >>> p=interpolatepol(v,[1,2,3,4],[3,2,4,1]); p
    (Fraction(15, 1))+(Fraction(-121, 6))*v+(Fraction(19, 2))*v**2+(Fraction(-4, 3))*v**3
    >>> y=[p.value(x) for x in [1,2,3,4]]; y
    [Fraction(3, 1), Fraction(2, 1), Fraction(4, 1), Fraction(1, 1)]
    >>> y==[3,2,4,1]
    True
    """
    from fractions import Fraction
    a = len(x) * [0]
    t = y[:]
    for i in range(len(x)):
        for k in range(i)[::-1]:
            t[k] = Fraction(t[k + 1] - t[k], x[i] - x[k])
        a[i] = t[0]
    p = a[-1]
    for i in range(len(x) - 1)[::-1]:
        p = p * (v - x[i]) + a[i]
    if all(c.denominator == 1 for c in p.coeffs):
        return lpol([c.numerator for c in p.coeffs], p.val, p.vname)
    else:
        return p
