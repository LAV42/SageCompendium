from sage.categories.sets_cat import Sets
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.list_clone import ClonableArray
from sage.structure.parent import Parent
from sage.combinat.partitions import ZS1_iterator
from sage.combinat.partitions import ZS1_iterator_nk
from sage.misc.flatten import flatten
import itertools
import numpy
from sage.arith.srange import srange
from sage.misc.prandom import randint
from sage.structure.richcmp import op_LT, op_LE, op_EQ, op_NE, op_GT, op_GE
from collections import Counter
from sage.functions.other import factorial
from sage.misc.misc_c import prod
from sage.combinat.partition import Partition


class BosonicPartition(ClonableArray):
    """Class for the standard partition."""

    def check(self):
        """Sanity check."""
        if not all(k >= 0 for k in iter(self)):
            raise ValueError(
                "The parts must greater than 0.")
        if not all(k == int(k) for k in iter(self)):
            raise ValueError(
                "The parts must be integers.")
        if len(self) <= 1:
            pass
        else:
            for i in range(len(self) - 1):
                if self._getitem(i) < self._getitem(i + 1):
                    raise ValueError(
                        "The bosonic partition must " +
                        "contain parts " +
                        "that appear in decreasing order.")

    # def _repr_(self):
    #     """Return the partition as a nicely formated string."""
    #     msg = '(' + ', '.join(map(str, self)) + ')'
    #     return msg

    def _add_(self, other):
        """Concatenate two partitions and order the result."""
        new_partition = list(self) + list(other)
        new_partition.sort(reverse=True)
        return BosonicPartition(BosonicPartitions(), new_partition)

    def _richcmp_(self, other, op):
        comp = BosonicPartitions.compare_dominance(self, other)
        with_equals = [op_LE, op_GE, op_EQ]
        with_less = [op_LE, op_LT]
        with_greater = [op_GE, op_GT]
        if op in with_equals and comp == '==':
            return True
        elif op in with_less and comp == '<':
            return True
        elif op in with_greater and comp == '>':
            return True
        else:
            if op == op_NE:
                return True
            else:
                return False

    def degree(self):
        """Return the degree of partition."""
        return sum(self)

    def conjugate(self):
        """Return the conjugate partition."""
        parts = list(self)
        # Destroy the diagram column by column, adding each column
        # to the new partition
        eat_diagram = [
            [x - k for x in parts if x - k > 0] for k in range(parts[0])]
        conj_part = [len(y) for y in eat_diagram]
        B = BosonicPartitions()
        return B(conj_part)

    def terminal_diagram(self):
        sparts = Superpartitions()
        to_spart = sparts([[], list(self)])
        to_spart.terminal_diagram()

    def leg_length(self, *args):
        """Return the leg length associated with coordinates."""
        i, j = args
        return Partition(list(self)).leg_length(i-1, j-1)

    def arm_length(self, *args):
        """Return the arm length associated with coordinates."""
        i, j = args
        return Partition(list(self)).arm_length(i-1, j-1)


class BosonicPartitions(UniqueRepresentation, Parent):
    """Class of the set of bosonic partitions. Parent class."""

    def __init__(self, degree=None, length=None):
        """Custom implemantation of Partitions of integer."""
        Parent.__init__(self, category=Sets())
        self.degree = degree
        self.length = length

    Element = BosonicPartition

    def _repr_(self):
        if self.degree is None:
            return "The set of partitions."
        else:
            return ("Partitions of "
                    "degree {} and length {}"
                    ).format(str(self.degree), str(self.length))

    def _element_constructor_(self, *args, **kargs):
        return self.element_class(self, *args, **kargs)

    def __iter__(self):
        if self.degree is None:
            raise ValueError("No iterator over all partitions.")
        elif self.length is None:
            for a_part in ZS1_iterator(self.degree):
                yield self.element_class(self, a_part)
        else:
            for a_part in ZS1_iterator_nk(
                    self.degree - self.length, self.length):
                v = [i + 1 for i in a_part]
                adds = [1] * (self.length - len(v))
                yield self.element_class(self, v + adds)

    @staticmethod
    def compare_dominance(parta, partb):
        """Compare the dominance ordering on two partitions."""
        if list(parta) == list(partb):
            return '=='
        if parta.degree() != partb.degree():
            return 'Non-comparable'
        else:
            partial_sum_a = [
                sum(parta[:k + 1]) for k in range(len(parta))]
            partial_sum_b = [
                sum(partb[:k + 1]) for k in range(len(partb))]
        min_length = min(len(partial_sum_a), len(partial_sum_b))
        comparing = [
            partial_sum_a[x] - partial_sum_b[x] for x in range(min_length)]
        compare_a = [x >= 0 for x in comparing]
        compare_b = [x <= 0 for x in comparing]
        if all(compare_a):
            out = '>'
        elif all(compare_b):
            out = '<'
        else:
            out = 'Non-comparable'
        return out


class FermionicPartition(BosonicPartition):

    def check(self):
        if not all(k >= 0 for k in iter(self)):
            raise ValueError(
                "The parts must be >= 0.")
        if not all(k == int(k) for k in iter(self)):
            raise ValueError(
                "The parts must be integers.")
        if len(self) <= 1:
            pass
        else:
            for i in range(len(self) - 1):
                if self._getitem(i) <= self._getitem(i + 1):
                    raise ValueError(
                        "The fermionic partition must " +
                        "contain decreasing distinct parts >= 0")

    def _add_(self, other):
        newparts = list(self) + list(other)
        length = len(newparts)
        inv_number = (self.inversion(newparts) +
                      length * (length - 1) / 2)
        newparts.sort(reverse=True)
        if not all(newparts[k] > newparts[k + 1]
                   for k in range(len(newparts) - 1)):
            out = [0, FermionicPartition(FermionicPartitions(), [])]
        else:
            sign = ((-1)**inv_number)
            out = (sign, FermionicPartition(
                FermionicPartitions(), newparts))
        return out

    @staticmethod
    def inversion(aList):
        """Return the number of inversion of a list."""
        inv_list = [
            sum(
                [
                    1 for j in range(k, len(aList)) if aList[k] > aList[j]
                ])
            for k in range(len(aList) - 1)
        ]
        return sum(inv_list)


class FermionicPartitions(UniqueRepresentation, Parent):
    def __init__(self, n=None, m=None):
        Parent.__init__(self, category=Sets())
        self.degree = n
        self.ferm_degree = m
        # if n < m*(m-1)/2

    Element = FermionicPartition

    def _repr_(self):
        if self.degree is None and self.ferm_degree is None:
            return "The set of fermionic partitions"
        else:
            return ("Partitions of distinct parts of "
                    "degree {} and length {}"
                    ).format(str(self.degree), str(self.ferm_degree))

    def _element_constructor_(self, *args, **kargs):
        return self.element_class(self, *args, **kargs)

    def __iter__(self):
        n = self.degree
        m = self.ferm_degree

        for a_partition in iter(BosonicPartitions(n + m, m)):
            if all(a_partition[k] > a_partition[k + 1]
                   for k in range(len(a_partition) - 1)):
                new_partition = [x - 1 for x in a_partition]
                yield self.element_class(self, new_partition)


class Superpartition(ClonableArray):
    def __init__(self, parent, lst):
        Fp = FermionicPartitions()
        Bp = BosonicPartitions()
        bosonic_list = lst[1]
        if 0 in bosonic_list:
            bosonic_list = [x for x in bosonic_list if x != 0]
        spart = [Fp(lst[0]), Bp(bosonic_list)]
        ClonableArray.__init__(self, parent, spart)

    def check(self):
        if len(list(self)) != 2:
            raise ValueError("Invalid format for superpartition.")
        else:
            FermionicPartition(FermionicPartitions(), self[0]).check()
            BosonicPartition(BosonicPartitions(), self[1]).check()
            # raise ValueError("Invalid superpartition")

    def _add_(self, other):
        S = Superpartitions()
        thesign, ferm_part = self[0] + other[0]
        bos_part = self[1] + other[1]
        new_spart = S([ferm_part, bos_part])
        return [thesign, new_spart]

    def __len__(self):
        return len(self[0]) + len(self[1])

    def star(self):
        """Remove the circles from the diagram. Return Partition."""
        new_spart = flatten(map(list, self))
        new_spart.sort(reverse=True)
        while 0 in new_spart:
            new_spart.remove(0)
        new_spart = BosonicPartition(BosonicPartitions(), new_spart)
        return new_spart

    def circle_star(self):
        """Transform the circles into boxes."""
        new_ferm = [x + 1 for x in self[0]]
        new_bos = list(self[1])
        new_list = new_ferm + new_bos
        new_list.sort(reverse=True)
        new_partition = BosonicPartition(BosonicPartitions(), new_list)
        return new_partition

    def cells(self):
        """Return the cells of the superpartition."""
        """
            Note that we use the convention that the first cell is (1,1)
        """
        spart_star = self.star()
        part = Partition(list(spart_star))
        coordinates = part.cells()
        coordinates = [(x+1, y+1) for x, y in coordinates]
        return coordinates

    def all_cells(self):
        """Return the cells of the superpartition, counting circles."""
        """
            Note that we use the convention that the first cell is (1,1)
        """
        spart_star = self.circle_star()
        part = Partition(list(spart_star))
        coordinates = part.cells()
        coordinates = [(x+1, y+1) for x, y in coordinates]
        return coordinates

    def fermionic_cells(self):
        """Return the cells that are fermionic."""
        cells = self.cells()
        cells_and_circles = self.all_cells()
        circles = [x for x in cells_and_circles if x not in cells]
        coords = [(i, jprime)
                  for iprime, jprime in circles
                  for i, j in circles
                  if iprime > i
                  ]
        coords.sort()
        return coords

    def bosonic_cells(self):
        """Return the cells that are bosonic."""
        cells = self.cells()
        fermionic_cells = self.fermionic_cells()
        coords = [x for x in cells if x not in fermionic_cells]
        return coords

    def upper_hook_length(self, i, j, parameter):
        leg = self.circle_star().leg_length(i, j)
        arm = self.star().arm_length(i, j)
        return leg + parameter*(arm + 1)

    def lower_hook_length(self, i, j, parameter):
        leg = self.star().leg_length(i, j)
        arm = self.circle_star().arm_length(i, j)
        return leg + 1 + parameter*arm

    def partition_pair(self):
        return [self.star(), self.circle_star()]

    def z_lambda(self):
        spart = self
        part_dict = Counter(list(spart[1]))
        out = prod([
            k**part_dict[k] * factorial(part_dict[k])
            for k in part_dict.keys()])
        return out

    def conjugate(self):
        part_pair = self.partition_pair()
        conj_part_pair = [x.conjugate() for x in part_pair]
        return Superpartitions.partition_pair_to_spart(conj_part_pair)

    def fermionic_degree(self):
        """Return the number of circles on the diagram."""
        return len(self[0])

    def bosonic_degree(self):
        degs = [x.degree() for x in self]
        return sum(degs)

    def sector(self):
        return (self.bosonic_degree(), self.fermionic_degree())

    def get_smaller_sparts(self):
        sector = self.sector()
        sparts = Superpartitions(*sector)
        smaller = [x for x in sparts if x < self]
        smaller = Superpartitions.sort_by_dominance(smaller)
        return smaller

    def switch_notation(self, ordering_symbol='a', add_zeros=0):
        """Give a representation of the spart like the diagram."""
        fermionic_part = self[0]
        bosonic_part = self[1]

        fermions = [
            tuple([
                fermionic_part[x],
                'circle',
                tuple([ordering_symbol, x])
            ])
            for x in range(len(fermionic_part))
        ]
        bosons = [
            tuple([
                bosonic_part[x],
                'box',
                tuple([ordering_symbol])
            ])
            for x in range(len(bosonic_part))
        ]
        if add_zeros > 0:
            bosons += [tuple([0, 'box', tuple([''])])
                       for x in range(add_zeros)]
        notated_spart = fermions + bosons
        notated_spart.sort(reverse=True)
        return tuple(notated_spart)

    def _richcmp_(self, other, op):
        comp = Superpartitions.compare_dominance(self, other)
        with_equals = [op_LE, op_GE, op_EQ]
        with_less = [op_LE, op_LT]
        with_greater = [op_GE, op_GT]
        if op in with_equals and comp == '==':
            return True
        elif op in with_less and comp == '<':
            return True
        elif op in with_greater and comp == '>':
            return True
        elif op == op_NE:
            return not(hash(self) == hash(other))
        else:
            return False

    def terminal_diagram(self):
        """Draw the super young Diagram associated to a spart."""
        lines = [[unichr(9632) for x in range(k)]
                 for k in self[1]]
        lines += [[unichr(9632) for x in range(k)]
                  + [unichr(9675)] for k in self[0]]
        lines.sort(reverse=True, key=len)
        for line in lines:
            print(' '.join(line))
        print('')


class Superpartitions(UniqueRepresentation, Parent):
    def __init__(self, bosonic_degree=None, fermionic_degree=None):
        Parent.__init__(self, category=Sets())
        self.bosonic_degree = bosonic_degree
        self.fermionic_degree = fermionic_degree
        self.sector = [bosonic_degree, fermionic_degree]

    def _coerce_map_from_(self, S):
        if self in Superpartitions() and S in Superpartitions():
            return True
        else:
            return False

    Element = Superpartition

    def _element_constructor_(self, *args, **kargs):
        return self.element_class(self, *args, **kargs)

    def __contains__(self, x):
        if isinstance(x, Superpartition):
            return True
        elif isinstance(x, Superpartitions):
            return True
        else:
            return False

    def _an_element_(self):
        if self.bosonic_degree is None or self.fermionic_degree is None:
            return self([[3, 1, 0], [4, 2, 2]])
        else:
            spart_list = list(self)
            return spart_list[randint(0, len(spart_list))]

    def _repr_(self):
        n = self.bosonic_degree
        m = self.fermionic_degree
        if self.bosonic_degree is None and self.fermionic_degree is None:
            the_str = "superpartitions"
        elif n < m * (m - 1) / 2:
            the_str = ("an empty set of superparitions" +
                       "(bosonic degree too small)")
        else:
            the_str = "Superpartitions with "
            if self.bosonic_degree is None:
                the_str += "an arbitrary number of boxes and "
            else:
                the_str += str(self.bosonic_degree) + " boxes and "
            if self.fermionic_degree is None:
                the_str += "an arbitrary number of circles"
            else:
                the_str += str(self.fermionic_degree) + " circles"
        return the_str

    def __iter__(self):
        """Iterator over superpartitions."""
        if self.bosonic_degree is None or self.fermionic_degree is None:
            raise ValueError("No iterator implemented"
                             + " over all superpartitions.")
        n = self.bosonic_degree
        m = self.fermionic_degree
        min_boxes = m * (m - 1) / 2
        # Empty set ?
        if m > 0:
            the_range = srange(n, min_boxes - 1, -1)
        else:
            the_range = [0]
        for k in the_range:
            fermi_iter = iter(FermionicPartitions(k, m))
            boson_iter = iter(BosonicPartitions(n - k))
            for a_pair in itertools.product(fermi_iter, boson_iter):
                yield _Superpartitions(list(a_pair))
                # yield self.element_class(self, list(a_pair))

    @staticmethod
    def partition_pair_to_spart(part_pair):
        """Give superpartition associated to a partition pair."""
        part_star = list(part_pair[0])
        part_circ_star = list(part_pair[1])
        add_zeros = len(part_circ_star) - len(part_star)
        if add_zeros != 0:
            new_star = part_star + [0]
        else:
            new_star = part_star
        diff_list = [a - b for a, b in zip(part_circ_star, new_star)]
        fermionic_parts = []
        bosonic_parts = []
        for k in range(len(diff_list)):
            if diff_list[k] == 0:
                bosonic_parts += [part_circ_star[k]]
            elif diff_list[k] == 1:
                fermionic_parts += [new_star[k]]
            else:
                raise Exception("This should not happen.")
        sparts = Superpartitions()
        return sparts([fermionic_parts, bosonic_parts])

    @staticmethod
    def sort_by_dominance(spart_list):
        """Sort a spart list according to dominance rating."""
        score = [
            sum(
                [
                    1 for x in spart_list if x >= y
                ]) for y in spart_list
        ]
        what_would_sort = numpy.argsort(score)
        sorted_sparts = [spart_list[x] for x in what_would_sort]
        return sorted_sparts

    @classmethod
    def give_greatest_spart(cls, spart_list):
        """Return the greatest spart of a list."""
        if len(spart_list) == 1:
            return spart_list[0]
        sorted_list = cls.sort_by_dominance(spart_list)
        if not(sorted_list[0] > sorted_list[1]):
            print("The two largest elements are non-comparable")
            return []
        else:
            return sorted_list[0]

    @classmethod
    def switch_back(cls, alt_spart):
        """Convert the alternative notation back to a spart."""
        alt = list(alt_spart)
        fermionic = []
        bosonic = []
        for part in alt:
            value = part[0]
            type = part[1]
            if type == 'box':
                bosonic.append(value)
            elif type == 'circle':
                fermionic.append(value)
        return Superpartitions()([fermionic, bosonic])

    @staticmethod
    def compare_dominance(left, right):
        """Return either >, <, == or Non-comparable."""
        left_pair = left.partition_pair()
        right_pair = right.partition_pair()
        if list(left) == list(right):
            out = "=="
        elif left.sector() == right.sector():
            if all([x >= y for x, y in zip(left_pair, right_pair)]):
                out = ">"
            elif all([x <= y for x, y in zip(left_pair, right_pair)]):
                out = "<"
            else:
                out = "Non-comparable"
        else:
            out = "Non-comparable"
        return out


_Superpartitions = Superpartitions()
