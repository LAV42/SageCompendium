"""Allows the manipulation of superpolynomials in variables."""
from sage.interfaces.singular import singular
from superpartition import _Superpartitions, Superpartitions
from sage.rings.rational_field import QQ
from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from sage.functions.other import factorial
from sym_superfunct import unique_perm_list_elements 
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
    def _int_vec_is_ordered(self, intvec):
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
            # Make sure we exit as soon as we know since this is going to be
            # called quite a lot
            if not is_sorted:
                return False
        bosonic_part = [part
                        for (part, ferm) in zip(x_var, thetas)
                        if not ferm]
        # Here we keep the extra 0's because [4,2,0,1] is not ordered 
        # but [4,2,1,0] is 
        bosonic_part = [value for value in bosonic_part]
        if sorted(bosonic_part, reverse=True) == bosonic_part:
            # We don't have to `and` with previous result because
            # at this point is_sorted can't be True
            is_sorted = True

        return is_sorted


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

    def is_symmetric(self, expr):
        """Check if expr is symmetric in N variables."""
        N = self._N
        SN = self._SN
        Theta = self._theta_var
        X = self._x_var
        permutations = SN
        # We generate the permutations of the list of variables
        # Here we take permutations of length 1 since f is symmetric 
        # if f = K_ij f for all ij. 
        permVars = [['dtheta'] + permutation(Theta) + permutation(X)
                    for permutation in permutations
                    if permutation.length() == 1]
        # join everything as a big string
        maps_arg = [','.join(new_vars) for new_vars in permVars]
        # Dimensions for the future Singular matrix
        matrix_dim = (len(permVars), 2*N+1)
        # Code needed for the Matrix declaration
        # MM[i][j] where each row is a new permuation and j are the
        # theta_0, theta_1, ....
        matrix_declaration = ('matrix MM'+'[%d][%d]' % matrix_dim +
                              '=' + ','.join(maps_arg) + ';')
        singular.eval(matrix_declaration)
        # We define a variable to act as a Singular-Sage bridge
        out = singular.int(1)
        # We find out how Singular calls 'out' internaly
        singular_out = out.name()
        # We retrieve the Singular name of expr in the current session
        # so that we can call it from inside
        singular_expr = singular(expr).name()
        # Here we prepare what is going to be sent to Singular
        computemap = (
            # We set result to be true by default
            "int out = 1;"
            # This 'for' will loop over the rows of the Matrix
            # that is over every permutation of S_N
            "for(int i=1; i<=" + str(matrix_dim[0]) + "; i++){"
            # We define a map which will be the exchange operator
            "map f = basering, MM[i,1.." + str(matrix_dim[1]) + "];"
            # We apply the map and add the result to previous permutations
            "if(" + singular_expr + "!= f(" + singular_expr + ")){"
            "out = 0; break;};"
            "};" +
            # We define the 'out' known by Sage to be the Singular 'out'
            # This will update the value of out in Sage.
            singular_out + "= out;"
            "kill out;"
        )
        # We send all of this to singular
        singular.eval(computemap)
        return bool(out)

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
    def symmetrize(self, expr, condition=None, normalize='nbvar'):
        """Symmetrize (in superspace) a Singular expression."""
        r"""
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
        # We generate the permutations of the list of variables
        permVars = [['dtheta'] + permutation(Theta) + permutation(X)
                    for permutation in permutations]
        # join everything as a big string
        number_of_maps = len(permVars)
        maps_arg = [','.join(new_vars) for new_vars in permVars]
        # Dimensions for the future Singular matrix
        matrix_dim = (number_of_maps, 2*N+1)
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
            "kill out;"
        )
        # We send all of this to singular
        singular.eval(computemap)
        return out

    def var_to_monomials(self, expr, check_sym=True):
        if check_sym:
            if not self.is_symmetric(expr):
                print("This superpolynomial is not symmetric.")
                return 0
        sector = self.get_sector(expr)
        ferm_degree = sector[1]
        if ferm_degree == 0:
            theta_1_m = 1
        else:
            theta_1_m = ['theta_'+str(k) for k in range(ferm_degree)]
            theta_1_m = singular('*'.join(theta_1_m))
        # Here we only take the part of expr that is multiplied by 
        # theta_0...theta_ferm_degree because the rest of the expression
        # doesn't have more informations. 
        # the [1] is to select the power theta...^1
        # the [2] gives us the expression that multiplies theta...^1
        # Note that Singular indices start at 1
        projected_expr = expr.coef(theta_1_m)[1][2]

        theta_projected = theta_1_m*projected_expr
        # Now from this expression, we want to extract the coefficients
        # and superpartitions. To get the sign and multiplicity right, we must
        # make sure that the exponents of the x's are compatible with a
        # superpartition
        int_vecs = [mono.leadexp().sage() for mono in theta_projected]
        # Here I add a dummy element at the begining of int_vecs so that
        # indices matches those of theta_projected (which starts at 1)
        int_vecs = [None] + int_vecs
        is_ordered = self._int_vec_is_ordered
        valid_vec = [k
                     for k in range(1, theta_projected.size() + 1)
                     if is_ordered(int_vecs[k])]
        to_spart = self._int_vec_to_spart
        # TODO verify that the coef are in the right ring
        spart_coef = {to_spart(int_vecs[k]): theta_projected[k].leadcoef()
                      for k in valid_vec}
        return spart_coef

    def monomial(self, spart):
        N = self._N
        super_composition = ([str(part) for part in spart[0]] +
                             [part for part in spart[1]])
        add_zeros = [0 for k in range(N-len(super_composition))]
        super_composition = super_composition + add_zeros
        permutations = unique_perm_list_elements(super_composition)
        ferm_perms = [[int(k) for k in a_perm if isinstance(k, str)]
                      for a_perm in permutations]
        inversions = [number_of_inversions(ferm_perm)
                      for ferm_perm in ferm_perms]

        def id_val_to_term(index, val):
            if isinstance(val, str):
                out = 'theta_' + str(index) + '*x_' + str(index) + '^'+val
            else:
                out = 'x_' + str(index) + '^' + str(val)
            return out
        monos_as_lists = [
            [id_val_to_term(k, a_comp[k])
             for k in range(len(a_comp))
             if a_comp[k] != 0]
            for a_comp in permutations]
        nb_monos = len(monos_as_lists)
        ferm_degree = spart.fermionic_degree()
        over_all_sign = (((ferm_degree - 1) * ferm_degree) / 2)
        inversions = [over_all_sign + inv for inv in inversions]
        monos = ['(-1)^' + str(inversions[k]) + '*' +
                 '*'.join(monos_as_lists[k])
                 for k in range(nb_monos)]
        m_lambda = singular('+'.join(monos))
        return m_lambda

    def _slow_monomial(self, spart):
        N = self._N
        composition = list(spart[0]) + list(spart[1])
        super_ns_mono = self.ns_monomial(composition)
        if len(spart[0]) > 0:
            thetas = ['theta_%d' % (k)
                      for k in range(spart.fermionic_degree())]
            thetas = singular('*'.join(thetas))
            super_ns_mono = thetas*super_ns_mono
        symmed = self.symmetrize(super_ns_mono, len(composition))
        # For some reason I have to cast the number to QQ
        # Otherwise sage returns 0 for 1/normal. I have no idea why.
        normal = QQ(spart.n_lambda()*factorial(N - len(spart)))
        normal = singular(1/normal)
        super_mono = normal*symmed
        return super_mono


def number_of_inversions(aList):
    """Return the number of inversion of a list."""
    inv_list = [
        sum(
            [
                1 for j in range(k, len(aList)) if aList[k] > aList[j]
            ])
        for k in range(len(aList) - 1)
    ]
    return sum(inv_list)
