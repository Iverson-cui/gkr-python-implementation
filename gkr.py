# from calendar import leapdays
from math import log2
from random import randint
from sumcheck import *


# the chi functions we need for multilinear extensions (see Thaler's section on MLE), which is also called multilinear lagrange basis polynomial.
def chi(w, x):
    prod = 1
    for i in range(len(x)):
        prod = prod * (x[i] * w[i] + (1 - x[i]) * (1 - w[i]))
    return prod


# find multilinear extension. A multilinear extension converts a function defined only on n binary inputs into a function defined on arbitrary n-tuples of elements from the ambient finite field.
def ext(f, variable_length, x):
    """
    x is a list of finite field element of length variable_length acting as the input to the f_tilde
    variable_length is the number of variables in the function f
    f is a function that takes a list of binary inputs

    This ext function calculate the result of the MLE of a binary input function f evaluated at x.
    """
    # acc is the final result.
    acc = 0
    w = Convert(generate_binary_strings(variable_length))
    for i in range(len(w)):
        w[i] = Convert(w[i])
        for j in range(len(w[i])):
            w[i][j] = int(w[i][j])
    for k in range(len(w)):
        acc += f(w[k]) * (chi(w[k], x))
    return acc % p


# define a binary tree to represent our arithmetic circuit. A value of '+' in the node will represent addition, while '*' will represent multiplication


# First for a node in the circuit, we define a class Node.
# binary_index is the gate label of the node in the layer. It's a list like [0, 1] or [1, 0, 1]
class Node:
    def __init__(self, binary_index, value, left=None, right=None):
        self.binary_index = binary_index
        self.value = value
        self.left = left
        self.right = right


# Here we create a circuit class which is built from the binary trees we defined above.
class Circuit:
    def __init__(self, layer_sizes=[1, 2, 2]):
        """
        layer_sizes is a list of integers, each representing the size of a layer in the circuit. The number of gates in a given layer is 2^size. But in this case it's 2^size+3, extra 3 gates are reserved for special functions.

        self.layers is a list of lists, each containing the same number of None elements at the gate number in this layer.

        for example:
        layer_sizes = [1, 2, 2]
        self.layers=[
        [None, None, None, None, None],           # Layer 0: 5=2+3 slots
        [None, None, None, None, None, None, None], # Layer 1: 7=4+3 slots
        [None, None, None, None, None, None, None]  # Layer 2: 7=4+3 slots
        ]

        The element in this 2D lists will be Node objects or Functions.
        """
        self.layers = list(map(lambda size: [None] * (2**size + 3), layer_sizes))

    def get_node(self, layer, index):
        """
        return the node at a given layer and index
        for the self.layers above, it's a 2d list. like [1][3] can be used to access a specific element.
        """
        return self.layers[layer][index]

    def add_node(self, layer, index, binary_index, value, left=None, right=None):
        """
        assign a node to a specific layer and index in the circuit.

        binary_index is the binary version of index. Former is used in the Node.__init__ method, latter is used to get access in the layer list.
        """
        self.layers[layer][index] = Node(binary_index, value, left, right)

    def add_func(self, layer, index, func):
        """
        Similar to add_node, assign a function to a specific layer and index in the circuit.

        This is specifically used for the extra 3 nodes in a layer.
        """
        self.layers[layer][index] = func

    def depth(self):
        """
        return the number of layers, i.e. the depth of the circuit.
        """
        return len(self.layers)

    def layer_length(self, layer):
        """
        return the number of nodes in a given layer, which is 2^size + 3.
        """
        return len(self.layers[layer])

    def layer_bits(self, layer):
        """
        return the number of bits needed to represent the nodes in a given layer.

        THIS MAY HAVE BUGS! for 5 gate, int(log2(5)) = 2, but we actually need 3 bits to represent indices 0-4. Safer way is to ceil from math. ceil(log2(self.layer_length(layer)))
        """
        return int(log2(self.layer_length(layer)))

    def add(self, layer, index, left, right):
        """
        check if a node at index of layer is an addition node with left and right children.

        If left, right is correct, node is "+", return int(True)= 1, else return int(False)=0.
        """
        node = self.get_node(layer, index)
        return int(
            (node.left == left) and (node.right == right) and (node.value == "+")
        )

    def mult(self, layer, index, left, right):
        """
        check if a node at index of layer is a multiplication node with left and right children.

        If left, right is correct, node is "*", return int(True)= 1, else return int(False)=0.
        """
        node = self.get_node(layer, index)
        return int(
            (node.left == left) and (node.right == right) and (node.value == "*")
        )


def get_binary_index(Node):
    return Node.binary_index


# Calculates and returns the value stored in a given node of a circuit.
def valueataNode(Node):
    """
    Calculate the output value of a node using recursion.
    """

    # base case: input layer node
    if Node.left == None and Node.right == None:
        return Node.value
    # recursive case: only input layer nodes have values of int, other nodes have values of "+" or "*"
    elif Node.value == "*":
        return valueataNode(Node.left) * valueataNode(Node.right)
    elif Node.value == "+":
        return valueataNode(Node.left) + valueataNode(Node.right)


def Wpoly(circuit, i, index):
    """
    Return the value of the node at layer i and index in the circuit.

    The reason why it's called Wpoly may be because some special node represents Wpoly.
    """
    return valueataNode(circuit.get_node(i, index))


def circuit_add(circuit, layer, w_list):
    """
    w_list is a list of three elements, where w_list[0] is the index of the node in the layer, and w_list[1] and w_list[2] are the indices of the left and right children respectively.

    This function checks if in layer, node with index w_list[0] is an addition node with left and right children at indices w_list[1] and w_list[2].

    THIS MAY HAVE BUGS! node and its branches should not be in the same layer, but here 3 nodes have the same layer.
    """
    left_node = circuit.get_node(layer, w_list[1])
    right_node = circuit.get_node(layer, w_list[2])
    return circuit.add(layer, w_list[0], left_node, right_node)


def circuit_mult(circuit, layer, w_list):
    """
    Similar with circuit_add function.
    """
    left_node = circuit.get_node(layer, w_list[1])
    right_node = circuit.get_node(layer, w_list[2])
    return circuit.mult(layer, w_list[0], left_node, right_node)


# We reduce verification at two points into verification at a single point using this ell function. See the Thaler notes for more on this technique.
def ell(p1, p2, t):
    """
    Reducing from two points to a single point.

    p1 and p2 are lists of finite field elements, which is the random challenge at the end of one round of GKR protocol. Like W(p1) and W(p2). Reducing it into a single point W(output).

    len(p1) is the number of variables. represent each variable with a line ax+b. b is consts and a is the other_term. b=p1 and a=p2-p1. As a result, t=0, output=p1; t=1, output=p2.

    variable t is given. This is the random challenge given by the verifier.

    It returns a list of the same length with p1 and p2.
    """
    consts = p1
    output = [0] * len(p2)
    other_term = [0] * len(p2)
    for i in range(len(p2)):
        other_term[i] = p2[i] - consts[i]
    for i in range(len(p2)):
        output[i] = consts[i] + t * other_term[i]
    return output


# actual function defining the gkr protocol. The input D is a function representing the multilinear extension
# of the outputs of the circuit.
def gkr(D, circuit):
    """

    D is a function representing the multilinear extension of the outputs of the circuit. Circuit is the circuit we perform GKR on.

    This function reduces the claim about output, i.e. D, to the input layer, m[circuit_depth() - 1], and checks it with input layer. It return True or False.
    """
    # claims for each layer
    m = [0] * circuit.depth()
    # random challenge for each layer. This is a list of lists, because within a layer there are many challenges.
    z = [0] * circuit.depth()

    # THIS MAY HAVE BUGS! I don't know why calculate layer_length(0) - 3/2. I think it should be log2(layer_length(0) - 3).
    z[0] = [0] * int((circuit.layer_length(0) - 3) / 2)
    # assign random value to every element in z[0], which act as random challenges
    for i in range(len(z[0])):
        z[0][i] = randint(0, p - 1)

    # D is a function of binary inputs, m[0] returns the value of the multilinear extension of W_0 at z[0].

    # m[0] is supposed to be the value of the multilinear extension of W_0 at random challenge z[0].
    # THIS MAY HAVE BUGS! D is supposed to be a function that takes length log2(layer_length(0)-3) variables, but here we use (circuit.layer_length(0) - 3) / 2.
    m[0] = ext(D, (circuit.layer_length(0) - 3) / 2, z[0])
    for i in range(circuit.depth() - 1):

        def f(x):
            """
            x: list of containing i+1 layer variables, i.e. b and c. Like W_i+1(b) and W_i+1(c).

            This function returns the value of the sumcheck poly in layer i, given input x. z is already given in z[i]
            """
            # // means floor division, like 9 // 2 = 4, but x is an even number with great possibility.
            b = x[: (len(x) // 2)]
            c = x[len(x) // 2 :]
            return (
                # circuit.get_node(i, -1) is probably add(z,b,c) in layer i
                ext(
                    circuit.get_node(i, -1),
                    (circuit.layer_length(i + 1) - 3)
                    + ((circuit.layer_length(i) - 3) / 2),
                    z[i] + b + c,
                )
                # circuit.get_node(i + 1, -3) is probably W_i+1 tilde(b) and W_i+1 tilde(c) in layer i+1
                # The length is still confusing.
                * (
                    ext(
                        circuit.get_node(i + 1, -3),
                        (circuit.layer_length(i + 1) - 3) / 2,
                        b,
                    )
                    + ext(
                        circuit.get_node(i + 1, -3),
                        (circuit.layer_length(i + 1) - 3) / 2,
                        c,
                    )
                )
                # circuit.get_node(i, -2) is probably mult(z,b,c) in layer i
                + ext(
                    circuit.get_node(i, -2),
                    (circuit.layer_length(i + 1) - 3)
                    + (circuit.layer_length(i) - 3) / 2,
                    z[i] + b + c,
                )
                * (
                    ext(
                        circuit.get_node(i + 1, -3),
                        (circuit.layer_length(i + 1) - 3) / 2,
                        b,
                    )
                    * ext(
                        circuit.get_node(i + 1, -3),
                        (circuit.layer_length(i + 1) - 3) / 2,
                        c,
                    )
                )
            ) % p

        # m[i] is the claim, f is the function of the sumcheck poly. This checks if there are False within the sumcheck process.
        val = sumcheck(m[i], f, int((circuit.layer_length(i + 1) - 3)))
        if not val:
            return False
        # reduce verification to a single point
        else:
            r = get_r()
            # b_start and c_start are the first half and second half of the r
            b_star = r[0 : int((circuit.layer_length(i + 1) - 3) / 2)]
            c_star = r[
                int((circuit.layer_length(i + 1) - 3) / 2) : int(
                    (circuit.layer_length(i + 1) - 3)
                )
            ]
            # q_at_zero is the value of single variable poly obtained by reducing to a single evaluation evaluated at 0
            # q_at_zero is supposed to equal W_i+1(b_star)
            q_at_zero = ext(
                circuit.get_node(i + 1, -3),
                (circuit.layer_length(i + 1) - 3) / 2,
                ell(b_star, c_star, 0),
            )
            # q_at_one is the value of single variable poly obtained by reducing to a single evaluation evaluated at 1
            # q_at_one is supposed to equal W_i+1(b_star)+W_i+1(c_star)
            q_at_one = ext(
                circuit.get_node(i + 1, -3),
                (circuit.layer_length(i + 1) - 3) / 2,
                ell(b_star, c_star, 1),
            )

            def modified_f():
                return (
                    ext(
                        circuit.get_node(i, -1),
                        (circuit.layer_length(i + 1) - 3)
                        + ((circuit.layer_length(i) - 3) / 2),
                        z[i] + b_star + c_star,
                    )
                    * (q_at_zero + q_at_one)
                    + ext(
                        circuit.get_node(i, -2),
                        (circuit.layer_length(i + 1) - 3)
                        + (circuit.layer_length(i) - 3) / 2,
                        z[i] + b_star + c_star,
                    )
                    * (q_at_zero * q_at_one)
                    % p
                )

            # checks that q_0=z_1 and q_1=z_2, i.e. q_at_zero =W_i+1(p1) and q_at_one=W_i+1(p2).
            # I don't know if the checks here can work.
            if f(b_star + c_star) != modified_f():
                return False
            # check has passed. Now assign a random challenge: r_star for t.
            else:
                r_star = randint(0, p - 1)
                # assign z and m to prepare for the next round. In the next loop(round), m[i+1] is the claim.
                z[i + 1] = ell(b_star, c_star, r_star)
                m[i + 1] = ext(
                    circuit.get_node(i + 1, -3),
                    int((circuit.layer_length(i + 1) - 3) / 2),
                    ell(b_star, c_star, r_star),
                )

    # input check
    if m[circuit.depth() - 1] != ext(
        circuit.get_node(circuit.depth() - 1, -3),
        (circuit.layer_length(circuit.depth() - 1) - 3) / 2,
        z[circuit.depth() - 1],
    ):
        return False
    return True


# test circuit
c = Circuit()
a1 = Node([0], 36)
a2 = Node([1], 6)
b1 = Node([0, 0], 9)
b2 = Node([0, 1], 4)
b3 = Node([1, 0], 6)
b4 = Node([1, 1], 1)
c1 = Node([0, 0], 3)
c2 = Node([0, 1], 2)
c3 = Node([1, 0], 3)
c4 = Node([1, 1], 1)


# W0
c.add_node(0, 0, [0], 36, left=b1, right=b2)
c.add_node(0, 1, [1], 6, left=b3, right=b4)


def W0func(arr):
    if arr == [0]:
        return 25
    elif arr == [1]:
        return 160


c.add_func(0, 2, W0func)


def multlayerzero(arr):
    if arr == [0, 0, 0, 0, 1]:
        return 1
    elif arr == [1, 1, 0, 1, 1]:
        return 1
    else:
        return 0


def addlayerzero(arr):
    return 0


c.add_func(0, 3, multlayerzero)
c.add_func(0, 4, addlayerzero)


# W1
c.add_node(1, 0, [0, 0], 9, left=c1, right=c1)
c.add_node(1, 1, [0, 1], 4, left=c2, right=c2)
c.add_node(1, 2, [1, 0], 6, left=c2, right=c3)
c.add_node(1, 3, [1, 1], 1, left=c4, right=c4)


def W1Func(bitstring):
    if bitstring == [0, 0]:
        return 1
    elif bitstring == [0, 1]:
        return 25
    elif bitstring == [1, 0]:
        return 40
    elif bitstring == [1, 1]:
        return 4


c.add_func(1, 4, W1Func)


def multlayerone(arr):
    if arr == [0, 0, 0, 0, 0, 0]:
        return 1
    elif arr == [0, 1, 0, 1, 0, 1]:
        return 1
    elif arr == [1, 0, 0, 1, 1, 0]:
        return 1
    elif arr == [1, 1, 1, 1, 1, 1]:
        return 1
    else:
        return 0


def addlayerone(arr):
    return 0


c.add_func(1, 5, multlayerone)
c.add_func(1, 6, addlayerone)

# W2
c.add_node(2, 0, [0, 0], 3)
c.add_node(2, 1, [0, 1], 2)
c.add_node(2, 2, [1, 0], 3)
c.add_node(2, 3, [1, 1], 1)


def W2func(bitstring):
    if bitstring == [0, 0]:
        return 1
    elif bitstring == [0, 1]:
        return 5
    elif bitstring == [1, 0]:
        return 8
    elif bitstring == [1, 1]:
        return 2


c.add_func(2, 4, W2func)


def multlayertwo(arr):
    return 0


def addlayertwo(arr):
    return 0


c.add_func(2, 5, multlayertwo)
c.add_func(2, 6, addlayertwo)


def D_func(arr):
    if arr == [0]:
        return 25
    elif arr == [1]:
        return 160


def D_func_ext(arr):
    return ext(D_func, 1, arr)


print(gkr(D_func_ext, c))
