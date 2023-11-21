#!/usr/bin/env python3

import collections

from sage.all import *
from sage.misc.verbose import verbose
from sage.schemes.elliptic_curves.hom_composite import EllipticCurveHom_composite

from .klpt import KLPT_Context, DecompAlphaN

#####################################
#                                   #
#           EC Functions            #
#                                   #
#####################################

from .xonly import xPoint, xISOG

def Frob(P):
    r"""
    Given a point P on any elliptic curve over a finite field
    whose coefficients lie in the prime field,
    returns P evaluated in the frobenius endomorphism
    """
    E = P.curve()
    p = E.base_field().characteristic()
    return E(*(c**p for c in P))

#TODO: can save isogeny evaluations by adding coprime-order points and decomposing them again post-evaluation
#      - only makes sense for points defined over same fields... not so many of them
#TODO: √élu for last bunch of isogenies
#      - requires the fix from #34732 to be efficient -> wait for Sage 9.8
def chain_iso(kernelPointsIn, E):
    r"""
    Given points {P_1, ..., P_n} on curve E, outputs the isogeny
    whose kernel is generated by {P_1, ..., P_n}
    """
    Ei = E
    F2 = Ei.base_field()
    kernelPoints = kernelPointsIn[::-1]

    philist = []
    while kernelPoints:
        Ri, (l,e) = kernelPoints.pop()
        Ki = Ri.mul(l**(e-1))
        #print(f"{Ki.curve.lift_x(Ki.X).order() = }") for debugging
        phi = xISOG(Ei, Ki.X, l)
        Ei = phi.codomain()

        if e > 1:
            kernelPoints.append((Ri, (l, e-1)))
        kernelPoints = [(P.push(phi), order) for (P, order) in kernelPoints]

        philist.append(phi)

    return EllipticCurveHom_composite.from_factors(philist)

#####################################
#                                   #
#       Ideal helper functions      #
#                                   #
#####################################

#FIXME ideally (ha, ha) this shouldn't exist
def multiplyIdeals(I, J, beta=None):
    r"""
    Computes the product I*J of two quaternion ideals I, J.
    If the right order of I and the left order of J are of
    same type, but not equal, an isomorphism orders must be given.

    By Skolem-Noether, this isomorphism is given by conjugation by
    a quaternion beta.
    """
    if I.right_order() != J.left_order():
        assert beta, "Must provide automorphism"
        J = ~beta*J*beta
        assert I.right_order() == J.left_order(), "Orders does still not match"
    return I*J

#####################################
#                                   #
#     Ideal-Isogeny translation     #
#                                   #
#####################################

class Deuring_Context:
    r"""
    Helper to setup parameters for computing the Deuring correspondence.
    """
    def __init__(self, O0, E0, iota, facToExt, T, S=None, f=None, J=None):
        self.O0 = O0
        self.E0 = E0
        F2 = E0.base_field()
        assert F2.degree() == 2
        self.p = F2.characteristic()
        self.iota = iota
        self.facToExt = facToExt
        self.T = T
        self.S = S
        self.f = f
        self.J = J

        def eval_i(pt):
            r"""
            Given a point P on E_0, returns P evaluated in iota,
            where iota corresponds to i in O_0 under the isomorphism E_0 -> O_0
            """
            if not pt:
                return pt
            x,y = pt.xy()
            R = pt.base_ring()['x,y'].fraction_field()
            f,g = map(R, iota.rational_maps())
            try:
                return pt.curve()(f(x,y), g(x,y))
            except ZeroDivisionError:   # Point is in the kernel
                return pt.curve()(0)
        self.endo_i = eval_i
        self.endo_j = Frob


    @cached_method
    def twistE0(self, extdeg):
        r"""
        Returns a quadratic twist \widetilde{E_0} of E_0 over F_{p^2k}.
        The twist has its own isomorphism \widetilde{E_0} -> O_0
        """
        Fbig,A = self.E0.base_field().extension(extdeg,'A').objgen()
        E0big = self.E0.change_ring(Fbig)
        while True:
            D = Fbig.random_element()
            if not D.is_square():
                break
        _,_,_,a,b = E0big.a_invariants()
        assert E0big == EllipticCurve([a,b])
        E = EllipticCurve([a/D**2, b/D**3])
        assert E.is_isomorphic(E0big.quadratic_twist())
        E.twist_D = D       #FIXME adding this attribute is quite a hack

        R,(x,y) = Fbig['x,y'].fraction_field().objgens()
        f,g = map(R, self.iota.rational_maps())
        f = f(x=D*x) / D
        g = (g//y)(x=D*x) * y
        def eval_i(pt):
            if not pt:
                return pt
            x,y = pt.xy()
            return pt.curve()(f(x,y), g(x,y))
        E.endo_i = eval_i   #FIXME adding this attribute is quite a hack

        u = D**(self.p//2)
        def eval_j(pt):
            if not pt:
                return pt
            x,y = pt.xy()
            return pt.curve()(x**self.p * u**2, y**self.p * u**3)
        E.endo_j = eval_j   #FIXME adding this attribute is quite a hack

        return E


    def evalIdealElt(self, a, Q):
        r"""
        Given an endomorphism a and a point Q of
        order coprime to the denominator of a,
        returns a(Q)
        """
        assert Q
        d = lcm(c.denominator() for c in a)
        E = Q.curve()
        twist = hasattr(E, 'twist_D')
        if not twist:
            iQ = self.endo_i(Q)
            jQ = self.endo_j(Q)
            kQ = self.endo_i(jQ)
        else:
            iQ = E.endo_i(Q)
            jQ = E.endo_j(Q)
            kQ = E.endo_i(jQ)
        coeffs = [coeff % Q.order() for coeff in a]
        aQ = coeffs[0]*Q + coeffs[1]*iQ + coeffs[2]*jQ + coeffs[3]*kQ
        return aQ, (E.twist_D if twist else 1)

    def IdealToIsogenyGens(self, I, specificTorsion=0):
        r"""
        Given a left O0-ideal I, returns {P_1, .., P_n} such that ker phi_I = <P_1, .., P_n>
        """
        kerGens = []
        a = DecompAlphaN(I)
        d = lcm(c.denominator() for c in a)
        N = ZZ(I.norm()).gcd(specificTorsion) if specificTorsion else ZZ(I.norm())
        for (l,e) in N.factor():
            lval = d.valuation(l)  # point divisions
            P, Q = self.genTorsionBasis(self.E0, l, e+lval)
            R,twD = self.evalIdealElt(l**lval * a.conjugate(), P)
            if not l**(e-1) * R:
                R,twD = self.evalIdealElt(l**lval * a.conjugate(), Q)
            kerGens.append((xPoint(R.xy()[0]*twD, self.E0.change_ring(R.base_ring())), (l,e)))
        return kerGens

    def IdealToIsogeny(self, I, specificTorsion=0):
        r"""
        Given a left O0-ideal I, returns the corresponding isogeny phi_I
        """
        kerGens = self.IdealToIsogenyGens(I, specificTorsion=specificTorsion)
        verbose("Evaluating isogeny...")
        return chain_iso(kerGens, self.E0)


    #####################################
    #                                   #
    # Sliding translation (Appendix A)  #
    #                                   #
    #####################################

    def dualIsoGens(self, phi, degree):
        r"""
        Given an isogeny phi and its degree,
        outputs a generating set of the kernel of the dual isogeny
        """
        facDeg = factor(degree)
        kerGens = []
        for (l,e) in facDeg:
            P, Q = self.genTorsionBasis(phi.domain(), l, e, xOnly=True)
            verbose(f"Finding kernel generator of order {l}^{e} over F_p^{P.curve.base_field().degree()}")
            R = P.push(phi)
            if not R.mul(l**(e-1)):
                R = Q.push(phi)
            kerGens.append((R, (l,e)))
        return kerGens

    def dualIso(self, phi, degree):
        r"""
        Given an isogeny phi and its degree,
        returns the dual of phi up to automorphisms
        """
        kerGens = self.dualIsoGens(phi, degree)
        phihat = chain_iso(kerGens, phi.codomain())
        varphi = phihat.codomain().isomorphism_to(phi.domain())  #TODO This might return the dual composed with some automorphism. Does it matter?
        return varphi * phihat

    def IdealToIsogenyCoprime(self, J, K, phi_K, alpha):
        r"""
        Given left O0-ideals J, K of coprime norms, phi_K and alpha such that
        J = K*\bar{alpha}/nrd(K), outputs phi_J
        """
        H1 = J + self.O0*self.T
        H2 = self.O0*alpha + self.O0*(J.norm()/H1.norm())

        verbose("--> Translating H1...")
        phi_H1 = self.IdealToIsogeny(H1)

        verbose("--> Translating H2...")
        ker_psi = self.IdealToIsogenyGens(H2)
        ker_psi = [(R.push(phi_K), deg) for (R, deg) in ker_psi]
        psi = chain_iso(ker_psi, phi_K.codomain())
        assert psi.codomain().j_invariant() == phi_H1.codomain().j_invariant()

        verbose("--> Moving precomputed basis")
        precompbasis = []
        for l, e in factor(H2.norm()):
            assert not l.divides(phi_K.degree())
            basis = self.genTorsionBasis(phi_K.domain(), l, e, xOnly=True)
            impts = tuple(T.push(phi_K) for T in basis)
            self.genTorsionBasis.set_cache(impts, phi_K.codomain(), l, e, xOnly=True)
        verbose("--> Computing the dual")
        psihat = self.dualIso(psi, psi.degree())
        varphi = phi_H1.codomain().isomorphism_to(psihat.domain())
        assert psihat.codomain() == phi_K.codomain()
        return psihat * varphi * phi_H1

    def IdealSlide(self, I, J, phi_J):
        r"""
        Given left O0-ideals I, J, phi_J, where I and J have coprime norm,
        such that I = J*Ii for some ideal Ii of norm S, outputs phi_Ii
        """
        assert self.O0 == I.left_order()
        I1 = I + self.O0*self.S

        print(f"Translating Ii of norm {factor(I1.norm())} to kernel")
        ker_I1 = self.IdealToIsogenyGens(I1)
        print("Pushing ker phi_I1 through phi_J")

        ker_phi1 = [(R.push(phi_J), deg) for (R, deg) in ker_I1]
        return chain_iso(ker_phi1, phi_J.codomain())

    def IdealFiltration(self, I):
        r"""
        Given an ideal I of norm dividing S^f, returns f ideals I_i,
        each of norm dividing S, such that I = I_1*I_2*...*I_f
        """
        ideals = []
        assert self.O0 == I.left_order()
        Ibuild = self.O0.unit_ideal()
        for i in range(1, self.f+1):
            I_i = Ibuild.conjugate()*I*(1/Ibuild.norm()) + Ibuild.right_order()*self.S
            Ibuild = Ibuild * I_i
            verbose(f"I_{i-1} has norm {factor(I_i.norm())}")
            ideals.append(I_i)
        assert Ibuild == I
        return ideals

    @cached_method
    def genTorsionBasis(self, E, l, e, xOnly=False):
        ### is there anything to be gained by using a more clever basis
        ### such that we do know the action of the endo ring on it?
        ### eg SIDH choice P, iota(P)
        r"""
        Given a curve E, prime l, exponent e, output generators (P, Q) of E[l^e]
        """
        t = l**e
        extdeg = self.facToExt[t]
        twist = not t.divides(self.p**extdeg - (-1)**extdeg)
        verbose(f"Generating torsion basis for E[{l}^{e}] over F_p^{2*extdeg}" + (" on quadratic twist" if twist else ""))

        if twist:
            assert E is self.E0
            E = self.twistE0(extdeg)
            Fbig = E.base_field()
        else:
            Fbig,A = E.base_field().extension(extdeg,'A').objgen()
            E = E.change_ring(Fbig)

        order = self.p**extdeg - (-1 if twist else +1) * (-1)**extdeg
        E.set_order(order**2, num_checks=0)
        assert t.divides(order)

        cof = order.prime_to_m_part(l)

        def rpt():
            while True:
                T = cof * E.random_point()
                Tl = l**(e-1)*T
                if Tl: break
            U = l*Tl
            while U:
                Tl = U
                U *= l
                T *= l
#            assert l**(e-1)*T and not l**e*T
#            assert Tl and not l*Tl
            T.set_order(l**e)
            Tl.set_order(l)
            return T, Tl

        P,Pl = rpt()
        Q,Ql = rpt()
        while Pl.weil_pairing(Ql,l).is_one():
            Q,Ql = rpt()

        if xOnly:
            D = E.twist_D if twist else 1
            P = xPoint(P.xy()[0]*D, self.E0.change_ring(Fbig))
            Q = xPoint(Q.xy()[0]*D, self.E0.change_ring(Fbig))
        return P, Q

    def IdealToIsogeny_S(self, I):
        r"""
        Given a left O0-ideal I of norm S^f, outputs phi_I
        """
        ctx = KLPT_Context(I.quaternion_algebra())

        verbose("----> Creating Ideal filtration")
        Ifilt = self.IdealFiltration(I)
        K = Ifilt[0]

        verbose(f"----> Translating K (of norm {factor(K.norm())}):")
        phi_K = self.IdealToIsogeny(K)

        verbose("----> Finding J equivalent (and of coprime norm) to K")
        beta, J, _, _, _, _ = ctx.KLPT(K, T=self.T**2, returnElem=True)

        verbose("----> Finding phi_J through IdealToIsogenyCoprime")
        phi_J = self.IdealToIsogenyCoprime(J, K, phi_K, beta)

        phiouts = []
        for index in range(1, len(Ifilt)):
            print(f"----> Passing part {index} out of {len(Ifilt) - 1}")
            Ii = multiplyIdeals(J, Ifilt[index], beta=beta.conjugate())
            phi_I1 = self.IdealSlide(Ii, J, phi_J)
            phiouts.append(phi_I1)

            if index == len(Ifilt) - 1:
                break

            K = K*Ifilt[index]
            print(f'norm(K) = {factor(K.norm())}')
            phi_K = phi_I1 * phi_K

            verbose("----> Finding J equivalent (and of coprime norm) to K")
            beta, J, _, _, _, _ = ctx.KLPT(K, T=self.T**2, returnElem=True)

            verbose("----> Finding phi_J through IdealToIsogenyCoprime")
            phi_J = self.IdealToIsogenyCoprime(J, K, phi_K, beta)

        return EllipticCurveHom_composite.from_factors(phiouts)


#####################################
#                                   #
#            Main/Wrapper           #
#                                   #
#####################################

def constructive_deuring(I, E0, iota, variant=None):
    r"""
    Given a curve E0, where End(E0) is isomorphic to O0 (a special
    p-extremal maximal order in the quaternion algebra B = <1,i,j,k>),
    the endomorphism iota corresponding to i, and a left O0 ideal I,
    outputs a curve E_I, whose endomorphism ring is isomorphic to the right order of I,
    and an isogeny phi_J : E_0 -> E_I of smooth norm.
    """
    O0 = I.left_order()
    KLPT_ctx = KLPT_Context(O0.quaternion_algebra())
    if not sage.misc.banner.require_version(9,8):
        EllipticCurveHom_composite.make_default()  #TODO remove once everyone runs Sage >= 9.8

    J, facToExt, T, S, f = KLPT_ctx.KLPT(I, variant=variant)
    print(f'norm(J) = {factor(J.norm())}')
    verbose(f'{J=}')
    assert gcd(J.left_order().unit_ideal().basis_matrix().solve_left(J.basis_matrix()).list()) == 1, 'non-cyclic ideal'

    grouped = collections.defaultdict(list)
    for le,k in sorted(facToExt.items()):
        grouped[k].append(le)
    print('Torsion by extension degree:')
    for k,les in sorted(grouped.items()):
        print(f'  {k:4}:  ', end='')
        for j,le in enumerate(les):
            print((', ' if j else '') + str(factor(le)), end='')
        print()

    Deuring_ctx = Deuring_Context(O0, E0, iota, facToExt, T, S, f, J)

    if S:
        print("Using fancier translation")
        print(f"Translating {f} ideals of norm dividing S = {factor(S)}, by coprime T = {factor(T)}")
        phi_I = Deuring_ctx.IdealToIsogeny_S(J)

    else:
        print("Using one-shot ideal-isogeny translation")
        phi_I = Deuring_ctx.IdealToIsogeny(J)

    return phi_I.codomain(), phi_I, Deuring_ctx
