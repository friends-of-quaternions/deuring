#!/usr/bin/env python3

from sage.all import *
from sage.misc.verbose import verbose
from sage.schemes.elliptic_curves.hom_composite import EllipticCurveHom_composite

def xDBL(a, b, X1):
    r"""
    Given an x-coordinate X1 = x(P) on the curve y^2 = x^3 + ax + b,
    returns the x-coordinate x([2]P).
    """
    # https://hyperelliptic.org/EFD/g1p/auto-code/shortw/xz/doubling/dbl-2002-it-2.op3
    # simplified using Z1=1
    T1 = X1**2
    T4 = T1-a
    T5 = T4**2
    T8 = b*X1
    T9 = 8*T8
    X3 = T5-T9
    T10 = T1+a
    T11 = X1*T10
    T13 = T11+b
    Z3 = 4*T13
    return X3/Z3

def xADD(a, b, X1, X2, X3):
    r"""
    Given x-coordinates X1 = x(P-Q), X2 = x(P), X3 = x(Q)
    on the curve y^2 = x^3 + a*x + b, returns the x-coordinate x(P+Q)
    """
    if X1:
        # https://hyperelliptic.org/EFD/g1p/auto-code/shortw/xz/diffadd/mdadd-2002-it-3.op3
        # simplified using Z2=Z3=1
        T1 = X2*X3
        T6 = T1-a
        T7 = T6**2
        T9 = 4*b
        T10 = X2+X3
        T11 = T9*T10
        X5 = T7-T11
        T13 = X2-X3
        T14 = T13**2
        Z5 = X1*T14
    else:
        # https://hyperelliptic.org/EFD/g1p/auto-code/shortw/xz/diffadd/mdadd-2002-it-2.op3
        # simplified using Z2=Z3=1
        t2 = X2*X3
        t5 = X2+X3
        t6 = t2+a
        t11 = 4*b
        t12 = t5*t6
        t13 = 2*t12
        R = t13+t11
        t16 = X2-X3
        S = t16**2
        t17 = S*X1
        X5 = R-t17
        Z5 = S
    return X5/Z5

def x_multiples(E, x):
    r"""
    Given an x-coordinate x(P), on the curve E,
    returns all the roots of the kernel polynomial of <P>.
    """
    _,_,_,a,b = E.a_invariants()
    assert E == EllipticCurve([a,b])
    if x is None:
        return []
    xs = [x]
    try:
        x = xDBL(a, b, x)
    except ZeroDivisionError:    # point of order two
#        assert x**3 + a*x + b == 0
        return xs
    while x not in xs[-2:]:
        xs.append(x)
        x = xADD(a, b, xs[-2], xs[-1], xs[0])
    return xs

################################################################

import ast
class _ntl_funs:
    r"""
    An object encapsulating the NTL context for a given finite
    field F, such that polynomials in F[X] can be converted to
    NTL using .ntlify() and minimal polynomials in F[X]/f can
    be computed using .minpoly_mod().
    """
    def __init__(self, F):
        self.ctx = ntl.ZZ_pEContext(ntl.ZZ_pX(F.modulus().list(), F.characteristic()))
        self.F = F
        self.R = F['X']

    def ntlify(self, poly):
        try:
            poly = poly.vector()
        except AttributeError:
            pass
        assert poly.base_ring() == self.F
        return ntl.ZZ_pEX([ntl.ZZ_pE(c.list(), self.ctx) for c in poly])

    def minpoly_mod(self, elt, mod):
        ntl_mod = self.ntlify(mod)
        ntl_elt = self.ntlify(elt) % ntl_mod
        ntl_res = ntl_elt.minpoly_mod(ntl_mod)
        return self.R(ast.literal_eval(str(ntl_res).replace(' ',',')))

@cached_function
def ntl_funs(F2):
    r"""
    Caching helper function to construct the _ntl_funs object
    for a given base field F2 of degree 2 over its prime field.
    """
    assert F2.degree() == 2
    return _ntl_funs(F2)

################################################################

class xPoint:
    r"""
    Class for x-only arithmetic on short Weierstrass curves.
    """
    def __init__(self, X, E):
        k = E.base_field()
        self.X = k(X) if X is not None else None
        self.curve = E

    def __repr__(self):
        return f"Point with X-coordinate {self.X} on {self.curve}"

    def __bool__(self):
        return self.X is not None

    def push(self, isogeny):
        r"""
        Given an isogeny phi (where phi is computed as a composition of isogenies
        computed with Kohel's algorithm), returns phi(self)
        """
        if type(isogeny) is not EllipticCurveHom_composite:
            isogeny = EllipticCurveHom_composite.from_factors([isogeny])

        newX = self.X

        for isopart in isogeny.factors():
            assert isinstance(isopart, EllipticCurveIsogeny)
            assert isopart._EllipticCurveIsogeny__algorithm == 'kohel'

            if (isom := isopart._EllipticCurveIsogeny__pre_isomorphism):
                newX = isom.x_rational_map()(newX)

            phi = isopart._EllipticCurveIsogeny__phi
            psi = isopart._EllipticCurveIsogeny__psi
            try:
                newX = phi(newX) / psi(newX)**2
            except ZeroDivisionError:
                verbose("Point seems to be in the kernel")
                newX = None
                return xPoint(None, isogeny.codomain())

            if (isom := isopart._EllipticCurveIsogeny__post_isomorphism):
                newX = isom.x_rational_map()(newX)

        new_curve = isogeny.codomain().base_extend(newX.parent())
        return xPoint(newX, new_curve)

    def dbl(self):
        r"""
        The x-only doubling map P -> [2]P
        """
        if not self:
            return self
        try:
            X = xDBL(self.curve.a4(), self.curve.a6(), self.X)
        except ZeroDivisionError:
            X = None
        return xPoint(X, self.curve)

    def add(self, other, diff):
        """
        The x-only map (P, Q, P-Q) -> P+Q
        """
        if not self:
            return other
        if not other:
            return self
        if not diff:
            assert self.X == other.X
            return self.dbl()
        assert self.curve == other.curve
        try:
            X = xADD(self.curve.a4(), self.curve.a6(), diff.X, self.X, other.X)
        except ZeroDivisionError:
            X = None
        return xPoint(X, self.curve)

    def mul(self, n):
        """
        Given an integer n, computes [n]self
        """
        n = ZZ(n).abs()
        if n == 0:
            return xPoint(None, self.curve)
        if n == 1:
            return self
        R0, R1, diff = self, self.dbl(), self
        for i in [int(b) for b in bin(n)[3:]]:
            R0pR1 = R0.add(R1, diff)
            diff = R0.add(R1, R0pR1)
            if i == 0:
                R0, R1 = R0.dbl(), R0pR1
            if i == 1:
                R0, R1 = R0pR1, R1.dbl()
        return R0


def kernel_polynomial_from_x(E, x, l):
    r"""
    Given the x-coordinate x(P), where P has order l,
    returns the kernel polynomial of <P>
    """
    F2 = E.base_field()
    Fbig = x.parent()
    ext = Fbig.over(F2)
    R,X = F2['X'].objgen()

    assert l.is_prime()
    if l <= 3:
        return R([-x, 1])

    try:
        X_in_F2 = F2(x)
    except ValueError:
        pass
    else:
        return prod(X - xx for xx in x_multiples(E, X_in_F2))

    if E.frobenius() not in ZZ:
        raise NotImplementedError

    def minpoly(elt):
        return ntl_funs(F2).minpoly_mod(ext(elt).vector(), ext.modulus())

    fs = [minpoly(x)]

    k = fs[0].degree()
    m = (l-1) // (2*k)

    assert k > 1    # handled above

    from sage.schemes.elliptic_curves.isogeny_small_degree import _least_semi_primitive
    a = _least_semi_primitive(l)

    xi = xPoint(x, E.change_ring(Fbig))
    for _ in range(1, m):
        xi = xi.mul(a)
        fs.append(minpoly(xi.X))

    return prod(fs)

################################################################

def xMUL(E, x, n):
    r"""
    Given an integer n, and x = x(P) of a point P on E, computes x([n]P)
    """
    Q = xPoint(x, E).mul(n)
    if not Q:
        raise ZeroDivisionError
    return Q.X

def xISOG(E, x, l):
    r"""
    Given a x = x(P) of a point P on E of order l,
    computes the separable isogeny with <P> as kernel
    """
    h = kernel_polynomial_from_x(E, x, l)
    return E.isogeny(h, check=False)
