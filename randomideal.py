#!/usr/bin/env python3

from sage.all import *

def random_ideal(O):
    r"""
    Sample an integral left O-ideal whose class is approximately uniform.
    """
    Q = O.quaternion_algebra()
    i,j,k = Q.gens()
    p = ZZ(Q.discriminant())
    assert p.is_pseudoprime()

    I = O.unit_ideal()
    for it in reversed(range(55+2*ceil(log(p,2)))):   #TODO figure out good bound
        O = I.right_order()
        while True:
            beta = sum(randint(1,10**4)*a for a in O.basis())
            if gcd(beta.reduced_norm(), 4) == 2:
                break
        J = O*2 + O*beta
        assert J.norm() == 2
        I *= J
        if not it or I.norm() >= p**(ZZ(2)/3):
            # find an ideal of smaller norm in the class
            _,mn = I.quadratic_form().__pari__().qfminim(None,None,1)
            el = sum(ZZ(c)*g for c,g in zip(mn, I.basis()))
            I *= el.conjugate() / I.norm()
#        print(f'{it:4}', I)
    return I

