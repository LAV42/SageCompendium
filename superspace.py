"""Allows the manipulation of superpolynomials in variables."""
from sage.interfaces.singular import singular
from superpartition import _Superpartitions, Superpartitions
from itertools import chain
import numpy as np
from sage.groups.perm_gps.permgroup_named import SymmetricGroup
singular.lib('nctools.lib')


class superspace:
    """General class for functions on variables in superspace."""

    def __init__(self, N, parameters=['q', 't', 'alpha']):
        """Define a superspace in 2*N+1 variables using singular."""
        x_var = ['x_'+str(k) for k in range(N)]
        theta_var = ['theta_'+str(k) for k in range(N)]
        names = (['dtheta'] + theta_var + x_var)

        name_str = '(' + ','.join(names) + ')'
        coeff_ring_str = '(0,' + ','.join(parameters) + ')'
        R = singular.ring(coeff_ring_str, name_str, 'lp')
        singular.setring(R)
        ER = singular.superCommutative(1, N+1)
        singular.setring(ER)
        # print(ER)
        for a_name in names:
            globals()[a_name] = singular(a_name)
        globals()['singular_vars'] = names
        globals()['dummy_odd'] = singular('dtheta')

        self._N = N
        self._SN = SymmetricGroup(range(N))
        self._param_names = parameters
        self._base_ring = ER
        self._x_var = x_var
        self._theta_var = theta_var

    def diff(self, expr, var, dtheta=None):
        """Differentiate in superspace."""
        if var*var == 0:
            if dtheta is None:
                dtheta = globals()['dummy_odd']
            new_expr = singular.substitute(expr, var, dtheta)
            new_expr = singular.diff(new_expr, dtheta)
        else:
            new_expr = singular.diff(new_expr, var)
        return new_expr

    def get_sector(self, expr):
        """Given an expression, return the sector to which it belongs."""
        vec = expr.leadexp().sage()
        N = self._N
        fermionic_degree = sum(vec[:N+1])
        bosonic_degree = sum(vec[N+1:])
        return (bosonic_degree, fermionic_degree)

    # TODO: Check if it works
    def _int_vec_is_ordered(self, intvec, return_spart=True):
        """Check wether the intvec taken from a supermonomial is a spart."""
        N = self._N
        thetas = intvec[1:N+1]
        x_var = intvec[N+1:]

        is_sorted = False

        fermionic_part = [part
                          for (part, ferm) in zip(x_var, thetas)
                          if ferm]
        if sorted(fermionic_part, reverse=True) == fermionic_part:
            is_sorted = True
        bosonic_part = [part
                        for (part, ferm) in zip(x_var, thetas)
                        if not ferm]
        bosonic_part = [value for value in bosonic_part if value != 0]
        if sorted(bosonic_part, reverse=True) == bosonic_part:
            is_sorted = True and is_sorted

        return _Superpartitions([fermionic_part, bosonic_part])

    # TODO: Check if it works.
    def _int_vec_to_spart(self, intvec):
        """Give the spart associated to the degree of a supermonomial."""
        """
            The intvec must be 2*N+1 dimensional, that is, it must
            include the Dummy fermionic variable index.
        """
        N = self._N

        # Retrieve which theta variables are present
        thetas = intvec[1:N+1]
        # Retrieve the x variables
        x_var = intvec[N+1:]

        # Fermionic parts are those which pair theta's and  x's of same index
        fermionic_part = [part
                          for (part, ferm) in zip(x_var, thetas)
                          if ferm]
        fermionic_part.sort(reverse=True)
        # Bosonic parts are the oposite
        bosonic_part = [part
                        for (part, ferm) in zip(x_var, thetas)
                        if not ferm]
        bosonic_part.sort(reverse=True)
        bosonic_part = [value for value in bosonic_part if value != 0]

        spart = _Superpartitions([fermionic_part, bosonic_part])
        return spart

    def ns_monomial(self, composition):
        """Return the monomial associated to composition."""
        N = self._N
        if len(composition) < N:
            composition = composition + [0
                                         for k in range(N - len(composition))]
        elif len(composition) > N:
            print('Composition too long')
            return 0
        x_var = self._x_var
        mono_str = '^%d*'.join(x_var) + '^%d'
        mono_str = mono_str % tuple(composition)
        mono = singular(mono_str)
        return mono

    def super_monomial(self, spart):
        """Return the monomial associated to spart."""
        N = self._N
        SN = self._SN

    def is_symmetric(self, expr):
        """Check if expr is symmetric."""
        N = self._N
        pass

    def apply_permuation(self, expr, permutation):
        Theta = self._theta_var
        X = self._x_var
        KwTheta = permutation(Theta)
        KwX = permutation(X)
        new_vars = ['dtheta'] + KwTheta + KwX
        perm_string = ','.join(new_vars)
        sing_map = singular('basering,'+perm_string, type='map')
        new_expr = sing_map(expr)
        return new_expr

    # There is still a bug somewhere
    # The factor in front of the whole thing is too big
    def symmetrize(self, expr, condition=None):
        """Symmetrize (in superspace) a Singular expression."""
        """
            Note that calling superspace.apply_permuation(expr) multiple times
            is not an option here since it is too slow. This function is fast
            because we send everything Singular needs to compute the result in
            a few operations only. Some operations are left in sage for the
            programmer convinience, but the idea is that we send all the
            permutations, (in maps_arg), as a Singular Matrix once which limits
            the number of times Sage has to give statements to Singular, this
            is typically the biggest bottleneck. The reason is that Sage
            is kind of typing everything in a internal singular_console().
        """
        N = self._N
        SN = self._SN
        Theta = self._theta_var
        X = self._x_var
        permutations = SN
        # TODO Remove permutation that leaves the initial monomial invariant
        if condition is not None:
            pass
        # We define all permutations of the variables
        permVars = [['dtheta'] + permutation(Theta) + permutation(X)
                    for permutation in permutations]
        # join everything as a big string
        maps_arg = [','.join(new_vars) for new_vars in permVars]
        # Dimensions for the future Singular matrix
        matrix_dim = (SN.cardinality(), 2*N+1)
        # Code needed for the Matrix declaration
        # MM[i][j] where each row is a new permuation and j are the 
        # theta_0, theta_1, ....
        matrix_declaration = ('matrix MM'+'[%d][%d]' % matrix_dim +
                              '=' + ','.join(maps_arg) + ';')
        singular.eval(matrix_declaration)
        # We define a variable to act as a Singular-Sage bridge
        out = singular.poly(0)
        # We find out how Singular calls 'out' internaly
        singular_out = out.name()
        # We retrieve the Singular name of expr in the current session
        # so that we can call it from inside
        singular_expr = singular(expr).name()
        # Here we prepare what is going to be sent to Singular
        computemap = (
            # We create an initial poly
            "poly out = 0;"
            # This 'for' will loop over the rows of the Matrix
            # that is over every permutation of S_N
            "for(int i=1; i<=" + str(matrix_dim[0]) + "; i++){"
            # We define a map which will be the exchange operator
            "map f = basering, MM[i,1.." + str(matrix_dim[1]) + "];"
            # We apply the map and add the result to previous permutations
            "out = out + f(" + singular_expr + ");"
            "};" +
            # We define the 'out' known by Sage to be the Singular 'out'
            # This will update the value of out in Sage.
            singular_out + "= out;"
        )
        # We send all of this to singular
        singular.eval(computemap)
        return out

    def symmetrize_old(self, expr):
        SN = self._SN
        perms = [self.apply_permuation(expr, perm) for perm in SN]
        symmed = sum(perms)
        return symmed

    def var_to_monomials():
        pass

    def monomial(self, spart):
        composition = list(spart[0]) + list(spart[1])
        super_ns_mono = self.ns_monomial(composition)
        if len(spart[0]) > 0:
            thetas = ['theta_%d' % (k) for k in range(spart.fermionic_degree())]
            thetas = singular('*'.join(thetas))
            super_ns_mono = thetas*super_ns_mono
        out = 1/(spart.n_lambda())*self.symmetrize(super_ns_mono)
        return out

