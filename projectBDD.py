from contextlib import AbstractContextManager
import unittest
from pyeda.inter import *
from typing import Any, List

# Constants for variable names
X_VARIABLES = [bddvar(f"x{i}") for i in range(5)]
Y_VARIABLES = [bddvar(f"y{i}") for i in range(5)]

# Initialize the adjacency matrix for the graph
def initialize_graph() -> List[List[bool]]:
    graph = [[False] * 32 for _ in range(32)]
    for i in range(32):
        for j in range(32):
            # Set graph edges based on specified conditions
            if (i + 3) % 32 == j % 32 or (i + 8) % 32 == j % 32:
                graph[i][j] = True

    return graph

# Create a Boolean expression for a given node value and variable
def create_boolean_expression(node_value, var):
    binary_representation = format(node_value, 'b').rjust(5, '0')
    bdd_string = []
    for i in range(5):
        variable_name = f"{var}{i}"
        # Include the variable or its negation based on the binary representation
        bdd_string.append(variable_name if binary_representation[i] == '1' else f"~{variable_name}")
    return expr("&".join(bdd_string))

# Create a BDD expression from a list of Boolean expressions
def create_bdd_expression_list(node_list, var):
    bdd_expression_list = [create_boolean_expression(i, var) for i in range(len(node_list)) if node_list[i]]
    bdd_expression = bdd_expression_list[0] if bdd_expression_list else expr(1)
    for expr in bdd_expression_list[1:]:
        bdd_expression |= expr
    return expr2bdd(bdd_expression)

# Find a specific node in a BDD given its value and associated variable
def find_node_in_bdd(bdd, node_value, var):
    binary_representation = format(node_value, 'b').rjust(5, '0')
    variable_list = [bddvar(f"{var}{i}") for i in range(5)]
    target_node = {variable_list[i]: int(binary_representation[i]) for i in range(5)}
    result = bdd.restrict(target_node)
    return result.is_one()

# Find a specific edge in a BDD given two node values
def find_edge_in_bdd(bdd, node_x, node_y):
    node_x_binary = format(node_x, 'b').rjust(5, '0')
    node_y_binary = format(node_y, 'b').rjust(5, '0')
    x_variable_list = [bddvar(f"x{i}") for i in range(5)]
    y_variable_list = [bddvar(f"y{i}") for i in range(5)]
    target_edge = {x_variable_list[i]: int(node_x_binary[i]) for i in range(5)}
    target_edge.update({y_variable_list[i]: int(node_y_binary[i]) for i in range(5)})
    result = bdd.restrict(target_edge)
    return result.is_one()

# Convert a graph represented as an adjacency matrix to a BDD
def graph_to_bdd(graph):
    R = [create_boolean_expression(i, 'x') & create_boolean_expression(j, 'y') for i in range(32) for j in range(32) if graph[i][j]]
    bdd_expression = R[0] if R else expr(0)
    for expr in R[1:]:
        bdd_expression |= expr
    return expr2bdd(bdd_expression)

# Apply a composition and smoothing operation on a BDD to compute RR2
def bdd_rr2(original_rr):
    tmp_variable_list = [bddvar(f"z{i}") for i in range(5)]
    x_variable_list = [bddvar(f"x{i}") for i in range(5)]
    y_variable_list = [bddvar(f"y{i}") for i in range(5)]
    composed_rr1 = original_rr.compose({x_variable_list[i]: tmp_variable_list[i] for i in range(5)})
    composed_rr2 = original_rr.compose({y_variable_list[i]: tmp_variable_list[i] for i in range(5)})
    return (composed_rr1 & composed_rr2).smoothing(tmp_variable_list)


# Compute the transitive closure of RR2
def bdd_rr2star(rr2):
    graph = initialize_graph()
    rr1 = graph_to_bdd(graph)
    rr2star = rr2
    while True:
        prev_rr2star = rr2star
        rr2star = bdd_rr2(rr2star)
        if rr2star.equivalent(prev_rr2star):
            break
    return rr2star

def evaluate_statement_a():
    prime_list = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    prime_bdd = create_bdd_expression_list([i in prime_list for i in range(32)], 'y')
    even_bdd = create_bdd_expression_list([i % 2 == 0 for i in range(32)], 'x')

    rr2star_for_prime = {}

    graph = initialize_graph()

    for u in range(32):
        if find_node_in_bdd(prime_bdd, u, 'y'):
            rr1 = graph_to_bdd(graph)
            rr2 = bdd_rr2(rr1)
            rr2_for_u = bdd_rr2star(rr2)
            rr2star_for_prime[u] = rr2_for_u
    
    for u, rr2star_u in rr2star_for_prime.items():
        exists_even_v = any(find_edge_in_bdd(rr2star_u, u, v) for v in range(32) if find_node_in_bdd(even_bdd, v, 'x'))
        if not exists_even_v:
            return False
    return True

result = evaluate_statement_a()
print("StatementA is true" if result else "StatementA is false")




# Unit test class for the graph functions
class TestGraph(unittest.TestCase):
    def setUp(self):
        self.even_list = [i % 2 == 0 for i in range(32)]
        self.prime_list = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        self.new_prime_list = [i in self.prime_list for i in range(32)]
        self.graph = initialize_graph()

    # Test even function
    def test_even(self):
        even_bdd = create_bdd_expression_list(self.even_list, 'x')
        self.assertTrue(find_node_in_bdd(even_bdd, 6, 'x'))
        self.assertFalse(find_node_in_bdd(even_bdd, 17, 'x'))

    # Test prime function
    def test_prime(self):
        prime_bdd = create_bdd_expression_list(self.new_prime_list, 'y')
        self.assertTrue(find_node_in_bdd(prime_bdd, 13, 'y'))
        self.assertFalse(find_node_in_bdd(prime_bdd, 2, 'y'))

    # Test RR function
    def test_rr(self):
        rr_bdd = graph_to_bdd(self.graph)
        self.assertTrue(find_edge_in_bdd(rr_bdd, 27, 3))
        self.assertFalse(find_edge_in_bdd(rr_bdd, 16, 20))

    # Test RR2 function
    def test_rr2(self):
        rr1 = graph_to_bdd(self.graph)
        rr2 = bdd_rr2(rr1)
        self.assertTrue(find_edge_in_bdd(rr2, 27, 6))
        self.assertFalse(find_edge_in_bdd(rr2, 27, 9))

    # Test RR2Star function
    def test_rr2star(self):
        rr1 = graph_to_bdd(self.graph)
        rr2 = bdd_rr2(rr1)
        rr2star = bdd_rr2star(rr2)
        self.assertTrue(find_edge_in_bdd(rr2star, 27, 3))
        self.assertTrue(find_edge_in_bdd(rr2star, 27, 6))
        self.assertFalse(find_edge_in_bdd(rr2star, 1, 15))





if __name__ == "__main__":
    unittest.main()

