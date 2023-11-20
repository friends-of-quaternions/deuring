#!/usr/bin/env python3

from sage.all import *
from sage.groups.generic import order_from_multiple
from sage.schemes.elliptic_curves.weierstrass_morphism import WeierstrassIsomorphism
from sage.schemes.elliptic_curves.hom_composite import EllipticCurveHom_composite

def mygens(E, B=2**20):
    r"""
    Generators the group of rational points, for elliptic curves
    with free rank-2 group structure.

    Monte-Carlo algorithm: Results will occasionally be wrong,
    depending on the size of B.
    """
    n = ZZ(E.order().sqrt())
    m = prod(l**e for l,e in n.factor(limit=B) if l<B)
    while True:
        P = E.random_point()
        Pm = (n//m)*P
        if order_from_multiple(Pm, m) == m:
            break
    while True:
        Q = E.random_point()
        Qm = (n//m)*Q
        if order_from_multiple(Pm.weil_pairing(Qm, m), m, operation='*') == m:
            break
    return P,Q

def torsion(E, d):
    r"""
    Generators of the d-torsion subgroup, possibly over field
    extensions, for elliptic curves with Frobenius [±p].
    """
    pi = ZZ(E.frobenius())
    assert pi.abs().is_prime()
    F = E.base_field()
    Fext = F.extension(Mod(pi,d).multiplicative_order(), 'a')
    Eext = E.change_ring(Fext)
    for _ in range(10):
        P,Q = mygens(Eext)
        P *= Eext.order().prime_to_m_part(d)
        Q *= Eext.order().prime_to_m_part(d)
        rem = Eext.order() // Eext.order().prime_to_m_part(d)
        P *= order_from_multiple(P,rem) // d
        Q *= order_from_multiple(Q,rem) // d
        if all(P.weil_pairing(Q,d)**(d//l) != 1 for l in d.prime_divisors()):
            break
    else:
        assert False, "extremely unlikely; bug?"
    P.set_order(d)
    Q.set_order(d)
    return P, Q

def frob(T):
    r"""
    Evaluate the Frobenius endomorphism of an elliptic curve
    defined over 𝔽p. Point may lie in an extension field.
    """
    p = T.curve().base_field().characteristic()
    return T.curve()(*(c**p for c in T))

def starting_curve(F):
    r"""
    Construct a starting curve over a given model of 𝔽p², using
    Bröker's algorithm and Ibukiyama's maximal orders.
    """
    from sage.rings.finite_rings.finite_field_base import FiniteField
    if not isinstance(F, FiniteField) or F.degree() != 2:
        raise TypeError('not 𝔽p²')

    p = F.characteristic()
    if p == 2:
        raise NotImplementedError('not implemented for characteristic 2')

    if p % 4 == 3:
        q = 1
        E = EllipticCurve(GF(p), [1,0])
        E.set_order(p + 1)
        EE = E.change_ring(F)
        iota,_ = sorted(a for a in EE.automorphisms() if a**4 != a**2)

    else:
        for q in map(ZZ, range(3,p,4)):
            if not q.is_prime():
                continue
            if legendre_symbol(-q, p) == -1:
                break
        else:
            assert False  # should never happen

        H = hilbert_class_polynomial(fundamental_discriminant(-q))
        jinv = H.change_ring(GF(p)).any_root()

        if jinv == 0:
            E = EllipticCurve(GF(p), [0,1])
        else:
            a = 27 * jinv / (4 * (1728-jinv))
            E = EllipticCurve(GF(p), [a,-a])
        E.set_order(p + 1)
        EE = E.change_ring(F)

        if 3 <= q <= (p+3)//4:
            iso = WeierstrassIsomorphism(None, (F(-q).sqrt(),0,0,0), EE)
            if q == 3 and EE.a_invariants() == (0,0,0,0,1):
                iota = EE.isogeny(EE(0,1))
            else:
                iota = EE.isogeny(None, iso.domain(), degree=q)
            iota = iso * iota

        else:
            iotas = set()
            for phi in EE.isogenies_prime_degree(q):
                for iso in phi.codomain().isomorphisms(EE):
                    iotas.add(iso * phi)
            iotas = list(iotas)

            # match up dual pairs of endomorphisms
            ext = ceil((2*q).log(p))
            P,Q = mygens(EE.change_ring(EE.base_field().extension(ext,'a')))
            iotas2 = []
            while iotas:
                iota = iotas.pop()
                imP,imQ = map(iota._eval, (P,Q))
                idxs = [idx for idx,dual in enumerate(iotas)
                        if dual._eval(imP)==q*P and dual._eval(imQ)==q*Q]
                if len(idxs) != 1: raise NotImplementedError
                idx, = idxs
                if iotas[idx] == -iota:                                         # tr = 0
                    iotas2.append(iota)
                    iotas2.append(iotas[idx])
                del iotas[idx]

            P,Q,_ = filter(bool, EE(0).division_points(2))
            iotas = [iota for iota in iotas2 if iota(P)==P and iota(Q)==Q]      # 2 | (1+i)
            if len(iotas) != 2:
                raise NotImplementedError
            iota = min(iotas)

    Quat,(i,j,k) = QuaternionAlgebra(-q, -p).objgens()

    if p % 4 == 3:
        maxords = {
                (i+j)/2: Quat.quaternion_order([1, i, (i+j)/2, (1+k)/2]),
            }

    elif p % 3 == 2:
        maxords = {
                (i+k)/3: Quat.quaternion_order([1, (1+i)/2, (j+k)/2, (i+k)/3]),
            }

    else:
        c = min(map(ZZ, Mod(-p,q).sqrt(all=True)))
        maxords = {
                (c*i+k)/q: Quat.quaternion_order([Quat.one(), (1+i)/2, (j+k)/2, (c*i+k)/q]),
                (c*i-k)/q: Quat.quaternion_order([Quat.one(), (1+i)/2, (j+k)/2, (c*i-k)/q]),
            }

    for O in maxords.values():
        assert O.discriminant() == Quat.discriminant()

    for test, O in maxords.items():
        d = test.denominator()
        assert d > 1
        P,Q = torsion(EE, d)
        for T in (P,Q):
            iT = iota._eval(T)
            jT = frob(T)
            kT = iota._eval(jT)
            im = sum(ZZ(c)*gT for c,gT in zip(d*test, (T,iT,jT,kT)))
            if im:
                break
        else:
            break
    else:
        assert False

    return EE, iota, O

################################################################

if __name__ == '__main__':
    r"""
    Test correctness of the algorithm for all p between 5 and 1000.
    """
    for p in primes(5, 1000):
        E, iota, O = starting_curve(GF(p**2))
        print(E)
        for g in O.basis():
            d = lcm(c.denominator() for c in g)
            if d == 1:
                continue
            print(g)
            P,Q = torsion(E, d)
            A = AdditiveAbelianGroupWrapper(P.parent(), [P,Q], [d,d])
            ims = []
            for T in (P,Q):
                iT = iota._eval(T)
                jT = frob(T)
                kT = iota._eval(jT)
                im = sum(ZZ(c)*gT for c,gT in zip(d*g, (T,iT,jT,kT)))
                ims.append(im)
            assert not any(ims)
        print(f'{p} ok')
