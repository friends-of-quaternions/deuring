#!/usr/bin/env python3
from sage.all import *
from sage.misc.verbose import verbose
from collections import defaultdict

r"""
Implements an algorithm that, given a left O_0-ideal I of norm N,
returns an equivalent ideal J~I of norm | R, where R can either be an input argument,
or where R is chosen so that it minimizes the cost of translating J
to its corresponding isogeny under the Deuring correspondence.

Requires that O_0 is a special p-extremal maximal order in the quaternion algebra B_{p,\infty}

Based on the seminal paper by Kohel, Lauter, Petit and Tignol: https://eprint.iacr.org/2014/505.pdf
"""

def cornacchiaFriendly(n, B=2**20):
    r"""
    Given a number n, checks if a n is "Cornacchia Friendly" (= easily factorable)
    """
    n = ZZ(n)
    if n < 0:
        return False
    if n < 2**160:
        return True
    l,_ = n.factor(limit=B)[-1]
    return l < 2**160 or is_pseudoprime(l)

def linearCombinations(m):
    for a1 in range(0, m+1):
        for a2 in range(-m, m+1):
            for a3 in range(-m, m+1):
                for a4 in range(-m, m+1):
                    yield (a1, a2, a3, a4)

def elem_to_matrix(a, Mat_1, Mat_i, Mat_j, Mat_k, Fn):
    r"""
    Turns a quaternion a into the corresponding element in M2(Fn) given images of 1, i, j, k
    """
    return sum(Fn(c)*g for c,g in zip(a, (Mat_1,Mat_i,Mat_j,Mat_k)))

def DecompAlphaN(I):
    r"""
    Given an Integral ideal I, returns a quaternion a such that I = O*a + O*N
    """
    N = ZZ(I.norm())
    basis = I.basis()
    while True:
        a = sum([b*randint(0,50) for b in basis])
        if gcd(a.reduced_norm(), N**2) == N:    #TODO is this check correct when N is not squarefree?
            break
    assert I.left_order() * N + I.left_order() * a == I
    return a


class KLPT_Context:
    r"""
    Helper to setup parameters for use in the KLPT algorithm
    """

    def __init__(self, B):
        self.B = B
        self.i, self.j, self.k = B.gens()
        self.p = ZZ(-self.j**2)
        self.q = ZZ(-self.i**2)
        self.QF = BinaryQF([1,0,self.q])

    def reducedBasis(self, I):
        r"""
        Given an integral ideal I, returns a Minkowski-reduced basis of I
        """
        M = I.basis_matrix()
        S = 2**ceil(log(self.p*self.q, 2))  #TODO figure out the optimal value for this
        D = diagonal_matrix(round(S * sqrt(g.reduced_norm())) for g in self.B.basis())
        return self.matrixToGens((M * D).LLL() * ~D)

    def matrixToGens(self, M):
        r"""
        Given a basis matrix M of an ideal of B, returns the corresponding generators (as quaternions)
        """
        return [sum(c*g for c,g in zip(row, self.B.basis())) for row in M]

    def equivalentPrimeIdeal(self, I, banned = []):
        r"""Given an integral ideal I, outputs a small (< p^(1/1.8)) prime-normed ideal in [I]
        If no such ideal is found, returns the smallest one found (with a warning)
        """
        verbose(f"trying to find of log(N) < (1/1.8)log(p) = {((1/1.8)*log(self.p,2)).n()}")
        Ibasis = self.reducedBasis(I)
        N = ZZ(I.norm())
        m = max(floor(log(self.p))//10,7)
        best = (0, +infinity)
        for a1,a2,a3,a4 in linearCombinations(m):
            delta = a1*Ibasis[0] + a2*Ibasis[1] + a3*Ibasis[2] + a4*Ibasis[3]
            dnorm = ZZ(delta.reduced_norm() / N)
            if 2 < dnorm < best[1] and dnorm.gcd(2*self.q)==1 and is_pseudoprime(dnorm) and I*(delta.conjugate()/N) not in banned:
                best = (delta, dnorm)
                verbose(f"log(N) = {log(dnorm,2).n()}")
                if log(dnorm,2) < (1/1.8)*log(self.p,2):
                    break
        if log(best[1],2) > (1/1.8)*log(self.p,2):
            print("Warning: KLPT might halt")
            print(f"Wanted norm < {(1/1.8)*log(self.p,2).n()}, got norm {log(best[1],2).n()}")
        return I*(best[0].conjugate()/N), best[0]

    # Easiest case R = Z[i] + jZ[i]
    def RepresentInteger(self, M):
        r"""
        Given a target integer, returns a quaternion in O_0 of reduced norm M
        """
        sol = None
        m = max(floor(sqrt(M/((1+self.q)*self.p))), 3)
        for z in range(1, m):
            for t in range(m):
                Mm = M - self.p*self.QF(z,t)
                if cornacchiaFriendly(Mm):
                    sol = self.QF.solve_integer(Mm)
                    if sol:
                        return sol[0] + self.i*sol[1] + self.j*(z + self.i*t)

    def IdealModConstraint(self, I, gamma, alpha):
        r"""
        Given an ideal I = O_0*alpha + O_0*N, and a gamma in O_0,
        returns a integers C,D such that mu = j*(C+i*D) satisfies O_0*gamma*mu/O_0*N = I/O_0*N
        """
        N = ZZ(I.norm())

        Mat_1 = identity_matrix(GF(N), 2)
        Mat_i, Mat_j, Mat_k = self.B.modp_splitting_data(N)
        assert Mat_i**2 == -self.q and Mat_j**2 == -self.p and Mat_j*Mat_i == -Mat_k

        # want:  gamma*(C*j-D*k) + (a+b*i+c*j+d*k)*alpha == 0
        els = [gamma*g for g in (self.j, -self.k)] + [g*alpha for g in self.B.basis()]
        mats = [elem_to_matrix(el, Mat_1, Mat_i, Mat_j, Mat_k, GF(N)) for el in els]
        eqs = matrix(GF(N), zip(*(mat.list() for mat in mats)))

        for sol in eqs.right_kernel().basis():
            if sol[:2] and sol[4:]:
                C,D = map(ZZ, sol[:2])
                assert I.left_order()*N + I.left_order()*(gamma*self.j*(C+self.i*D)) == I
                return C, D

    def StrongApproximation(self, N, facT, C, D):
        r"""
        Given the norm of I (N), the target norm (T) and
        the output from IdealModConstraint (C,D),
        outputs nu such that beta = gamma*nu is in I, and I*(gamma*nu/N) has norm T.

        Also described as using strong approximation on nu = j*(C+i*D)
        """
        T = prod([l**e for l,e in facT])
        R = Integers(N)
        R2 = Integers(N**2)
        lamsq = R(T) / (R(self.p) * self.QF(R(C), R(D)))
        if kronecker(lamsq, N) == -1:
            nonsq = 1
            for pri,e in facT:
                if kronecker(pri, N) == -1:
                    nonsq = pri
                    break
            else:
                return None
            T //= nonsq
            lamsq = R(T) / (R(self.p) * self.QF(R(C), R(D)))
        lam = sqrt(lamsq)
        sol = None
        Mat = Matrix(R, [2*R(self.p)*R(lam)*R(C), 2*R(self.q)*R(self.p)*R(lam)*R(D)])
        try:
            solslin = Mat.solve_right(vector([R(ZZ(R2(T) - R2(self.p)*self.QF(R2(lam)*R2(C), R2(lam)*R2(D)))//N)]))
        except ValueError:  #TODO figure out under what conditions this fails
            return None
        ker = Mat.right_kernel()
        # Improvement using shortest solutions from lattice
        a, b = solslin
        ker0, ker1 = ker.basis()[0]
        lam = ZZ(lam)
        Mat = Matrix(ZZ, [[N*ZZ(ker0), N*ZZ(ker1), 0],[N**2,0, 0], [0,N**2,0], [-lam*ZZ(C) - N*ZZ(a), -lam*ZZ(D)-N*ZZ(b), N**2]])
        for vec in Mat.LLL():
            if vec[-1] == N**2:
                x1 = -vec[0]
                y1 = -vec[1]
                M = T-self.p*self.QF(x1, y1)
                assert M%(N**2) == 0
                M = M // N**2
                verbose(f"{M=}")
                if cornacchiaFriendly(M):
                    verbose(f"Easily factorable!")
                    sol = self.QF.solve_integer(M)
                else:
                    sol = None
        if sol is None:
            return None
        z = (x1-lam*C)//N
        t = (y1-lam*D)//N
        return lam*self.j*(C+D*self.i) + N*(sol[0] + self.i*sol[1] + self.j*(z + self.i*t))

    def FindExtra(self, N, facT):
        r"""
        Helper function to find necessary output size of representInteger.
        """
        ex = 1
        while N*ex < 30*self.p:
            l, e = choice(facT)
            ex *= l
            facT.remove((l,e))
            if e > 1:
                facT.append((l, e-1))
        return ex, facT


    def KLPT(self, I, T=None, returnElem=False, variant=None):
        r"""
        Given an integral ideal I, and a target norm T,
        outputs an equivalent left ideal J~I, with nrd(J) dividing T.

        If target norm T is not given, T will be chosen to minimize
        the cost of translating J to its corresponding isogeny.
        """
        B = self.B
        p = self.p
        i,j,k = self.i, self.j, self.k

        O0 = I.left_order()
        assert O0.quaternion_algebra() == B

        origN = ZZ(I.norm())

        nu = None
        bannedIdeals = []

        while not nu:
            if 2 < origN < p**(ZZ(1)/2) and origN.gcd(2*self.q)==1 and is_pseudoprime(origN) and I not in bannedIdeals:
                verbose("I already prime and small")
                II = I
                alpha_marked = origN
            else:
                verbose("Finding equivalent prime ideal")
                II, alpha_marked = self.equivalentPrimeIdeal(I, banned = bannedIdeals)

            if variant is None:
                #TODO find crossover point if one exists
                variant = 'simple'

            N = ZZ(II.norm())
            if not T:
                from .cost import choose_torsion
                verbose("Finding output norm T")
                if variant == 'simple':
                    T, facToExt = choose_torsion(p, self.q, N, max(p*N**4, p**3))
                    fac = list(factor(T))
                    S = None
                    f = None
                elif variant == 'slide':
                    T, facToExt = choose_torsion(p, self.q, N, p**(4.2/2), newconst=(0.31, 15*1.17, 15*0.46, 15*0.01))
                    Tfactors = [l**e for (l,e) in factor(T)]
                    Tfactors.sort()
                    S = 1
                    for le in Tfactors:
                        if T/(S*le) < p**(3.2/2):
                            break
                        S *= le
                    T = T/S
                    f = ceil(log(max(p*N**4, p**3), S))
                    fac = list(factor(S**f))
                else:
                    raise NotImplementedError(f'unknown algorithm variant: {variant}')
            else:
                fac = list(factor(T))
                facToExt = None
                S = None
                f = None

            for _ in range(max(N//10, 5)):  # This is basically only a problem when N is tiny, i.e. < 100
                ex, facupdated = self.FindExtra(N,fac.copy())
                gamma = self.RepresentInteger(N*ex)
                if gamma:
                    alpha = DecompAlphaN(II)
                    CD = self.IdealModConstraint(II, gamma, alpha)
                    if CD is None:
                        continue
                    C, D = CD
                    if Mod(p,N) * self.QF(Mod(C,N), Mod(D,N)) and Mod(D,N):
                        nu = self.StrongApproximation(N, facupdated, C, D)
                if nu:
                    break
            if not nu:
                bannedIdeals.append(II)
                T = None

        beta = gamma*nu
        denom = gcd(O0.unit_ideal().basis_matrix().solve_left((II * (beta.conjugate()/N)).basis_matrix()).list())
        return_alpha = beta / denom * alpha_marked / N
        I *= return_alpha.conjugate() / I.norm()
        if returnElem:
            return return_alpha, I, facToExt, T, S, f
        return I, facToExt, T, S, f
