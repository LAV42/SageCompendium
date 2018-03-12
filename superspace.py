"""Allows the manipulation of superpolynomials in variables."""
from sage.interfaces.singular import singular
from superpartition import _Superpartitions, Superpartitions
import numpy as np
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
        self._param_names = parameters
        self._base_ring = ER
        self._var_even = x_var
        self._var_odd = theta_var

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

    def is_symmetric(self, expr):
        """Check if expr is symmetric."""
        N = self._N
        pass

    def apply_permuation(self, permutation):
        pass

    def var_to_monomials():
        pass

    def mono_expand(N, conditions = None):
        pass
