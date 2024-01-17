import sys
# -*- coding: utf-8 -*-
""" Make a beautiful TikZ drawing of a planar forest.

- A planar forest is beautiful if:
  - Each subtree is beautiful.
  - The subtrees are placed as compactly as possible, but with no two
    subtrees having a horizontal distance between them of less than one
    unit.
  - The root of each subtree are as evenly spaced out as possible.

- Trees are beautiful if:
  - The forest you get by removing the root of the tree is beautiful.
  - The vertical distance between the root and the next level of nodes
    is one unit.
  - The horizontal position of the root is the median of the horizontal
    positions of the roots of the subtrees.

- The one-node tree is beautiful.

- All nodes at the same level have the same vertical position.

planarforest is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation, either version 3 of the License, or (at your
option) any later version.

planarforest is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General
Public License for more details.

You should have received a copy of the GNU General Public License along
with planarforest. If not, see <http://www.gnu.org/licenses/>.

:Authors: Håkon Marthinsen
:Date: 2014-03-18
:Version: 4
:Contact: hakon.marthinsen@gmail.com
"""


class Node(object):
    """A node in a planar forest."""
    def __init__(self, children=None, color='b', x_pos=0.0, parent=None, inner_label = '', outer_label = '', label_direction = '0'):
        if children is None:
            children = []
        self.children = children
        self.color = color
        self.x_pos = x_pos
        self.parent = parent
        self.border_left = [0.0]
        self.border_right = [0.0]
        self.inner_label = inner_label
        self.outer_label = outer_label
        self.label_direction = label_direction

    def __repr__(self):
        string = f"Node({self.color}, {self.inner_label}, {self.outer_label})\n"

        if len(self.children) > 0:
            string += "--- Children ---\n"
            for child in self.children:
                string += repr(child).replace("\n","\n  ") + "\n"
            string += '---/Children/---\n'

        return string

    def __str__(self):
        inner_label = self.inner_label
        if self.outer_label != "":
            outer_label = f",label={{ [label distance=-1mm]{self.label_direction}:{{ \\scriptsize {self.outer_label} }} }}"
        else:
            outer_label = ""

        """Generate TikZ commands to draw the tree."""
        string = f"\\node [{self.color + outer_label}] at ({self.x_pos}, 0.0) {{ {inner_label} }} \n"
        for child in self.children:
            string += child.tikz()
        string += ";\n"
        return string

    def tikz(self, draw_edge = True):
        inner_label = self.inner_label
        if self.outer_label != "":
            outer_label = f",label={{ [label distance=-1mm]{self.label_direction}:{{ \\scriptsize {self.outer_label} }} }}"
        else:
            outer_label = ""

        draw_edge_string = ""
        if not draw_edge:
            draw_edge_string = "edge from parent[draw=none]"

        """Returns TikZ commands for drawing this subtree. Internal usage."""
        string = f"child {{node [{self.color + outer_label}] at ({self.x_pos - self.parent.x_pos}, 1.0) {{ {inner_label} }} {draw_edge_string} \n"
        for child in self.children:
            string += child.tikz()
        string += "}\n"
        return string

    def add_child(self, node):
        self.children.append(node)
        self.children[-1].parent = self

    def add_sibling(self, node):
        self.parent.add_child(node)

    def shift_x(self, offset):
        """
        Shift the whole subtree with self as root to the right by
        an amount equal to offset.
        """
        self.x_pos += offset
        self.border_left = [el + offset for el in self.border_left]
        self.border_right = [el + offset for el in self.border_right]
        for child in self.children:
            child.shift_x(offset)

    def optimize(self):
        """Arrange nodes of the tree optimally."""
        for child in self.children:
            child.optimize()

        if len(self.children) > 0:
            # Do nothing for leaves.

            # Arrange subtrees compactly.
            forest = Forest(self.children)
            forest.arrange_subtrees()
            self.border_left = forest.border_left[:]
            self.border_right = forest.border_right[:]

            # Place node at median of subtree root positions and convert to
            # relative coordinates.
            self.x_pos = median([child.x_pos for child in self.children])
            self.shift_x(-self.x_pos)

            self.border_left.insert(0, 0.0)
            self.border_right.insert(0, 0.0)

class Cycle(Node):

    def __repr__(self):
        string = f"Cycle\n--- Trees ---\n"
        for child in self.children:
            string += repr(child).replace("\n","\n  ") + "\n"
        string += '---/Trees/---\n'

        return string

    def __str__(self):
        string = ""

        for child1, child2 in zip(self.children[:-1], self.children[1:]):
            string += "\\draw ({0},1.0) edge ({1},1.0);\n".format(child1.x_pos, child2.x_pos)

        string += "\\draw ({0},1.0) arc (90:270:0.5);\n".format(self.children[0].x_pos)
        string += "\\draw ({0},1.0) arc (90:-90:0.5);\n".format(self.children[-1].x_pos)
        string += "\\draw ({0},0.0) edge ({1},0.0);\n".format(self.children[0].x_pos, self.children[-1].x_pos)

        string += f"\\node [draw=none] at ({self.x_pos}, 0.0) {{ }} \n"

        for child in self.children:
            string += child.tikz(draw_edge = False)

        string += ";\n"

        return string

    def optimize(self):
        super().optimize()

        self.border_left[0] = self.children[0].border_left[0] - 0.1
        self.border_right[0] = self.children[-1].border_right[0] + 0.1

class Stolon:

    def __init__(self, nodes = []):
        self.nodes = nodes

    def __repr__(self):
        return f"Stolon({', '.join([str(n.x_pos) for n in self.nodes])})\n"


    def __str__(self):
        string = ""

        for node1, node2 in zip(self.nodes[:-1], self.nodes[1:]):
            string += "\\draw ({0},-0.1) edge ({1},-0.1);\n".format(node1.x_pos, node2.x_pos)
            string += "\\draw ({0},0.1) edge ({1},0.1);\n".format(node1.x_pos, node2.x_pos)

        string += "\n"

        return string
    
    def append(self, node):
        self.nodes.append(node)

class Forest(object):
    def __init__(self, nodes=None, stolons=None):
        if nodes is None:
            nodes = []
        if stolons is None:
            stolons = []
        self.nodes = nodes
        self.stolons = stolons
        self.border_left = []
        self.border_right = []

    def __repr__(self):
        string = "Forest()\n--- Trees ---\n"
        for tree in self.nodes:
            string += repr(tree).replace("\n", "\n  ") + "\n"
        string += "---/Trees/---\n"

        return string

    def __str__(self):
        """Generate TikZ commands to draw the forest."""
        string = "\\tikz[planar forest] {\n"
        string += "\n"

        for stolon in self.stolons:
            string += str(stolon)

        for subtree in self.nodes:
            string += str(subtree)
        
        string += "}"
        return string

    def set_unit(self, unit):
        self.unit = unit

    def append(self, node):
        self.nodes.append(node)

    def optimize(self):
        for subtree in self.nodes:
            subtree.optimize()
        self.arrange_subtrees()

    def arrange_subtrees(self):
        # Place optimal subtrees compactly.
        # First scan from left to right.
        self.border_left = self.nodes[0].border_left[:]
        self.border_right = self.nodes[0].border_right[:]
        for subtree in self.nodes[1:]:
            for level in range(min(len(self.border_right),
                                   len(subtree.border_left))):
                delta = subtree.border_left[level] - self.border_right[level]
                if delta < 1:
                    subtree.shift_x(1.0 - delta)
            # Update borders
            self.border_left += subtree.border_left[len(self.border_left):]
            self.border_right = subtree.border_right + \
                self.border_right[len(subtree.border_right):]

        # Save the subtree positions for scan left to right and reset.
        pos_l_to_r = [subtree.x_pos for subtree in self.nodes]
        for subtree in self.nodes:
            subtree.shift_x(self.nodes[-1].x_pos - subtree.x_pos)

        # Next, scan from right to left while keeping the outer trees fixed.
        self.border_left = self.nodes[-1].border_left[:]
        self.border_right = self.nodes[-1].border_right[:]
        for subtree in reversed(self.nodes[:-1]):
            for level in range(min(len(self.border_left),
                                   len(subtree.border_right))):
                delta = self.border_left[level] - subtree.border_right[level]
                if delta < 1:
                    subtree.shift_x(delta - 1.0)
            # Update borders
            self.border_right += subtree.border_right[len(self.border_right):]
            self.border_left = subtree.border_left + \
                self.border_left[len(subtree.border_left):]

        # Save the subtree positions for scan right to left and reset middle
        # subtree positions.
        pos_r_to_l = [subtree.x_pos for subtree in self.nodes]
        for subtree in self.nodes[1:-1]:
            subtree.shift_x(self.nodes[0].x_pos - subtree.x_pos)

        # Place subtrees as close to evenly spaced out as possible.
        if len(self.nodes) > 1:
            optimal_dist = (pos_r_to_l[-1] -
                            pos_r_to_l[0]) / (len(self.nodes) - 1)
        for i in range(1, len(self.nodes) - 1):
            optimal_pos = i * optimal_dist + self.nodes[0].x_pos
            if optimal_pos < pos_l_to_r[i]:
                self.nodes[i].shift_x(pos_l_to_r[i] - self.nodes[i].x_pos)
            elif optimal_pos > pos_r_to_l[i]:
                self.nodes[i].shift_x(pos_r_to_l[i] - self.nodes[i].x_pos)
            else:
                self.nodes[i].shift_x(optimal_pos - self.nodes[i].x_pos)


def median(vector):
    """Calculate median of sorted vector."""
    length = len(vector)
    middle = length // 2
    if length % 2 == 1:
        return vector[middle]
    else:
        return 0.5 * (vector[middle] + vector[middle - 1])


def decode_node_info(string):
    color = ''
    inner_label = ''
    outer_label = ''
    label_direction = '0'
    if string.count('_') == 2:
        color, outer_label, label_direction = tuple( string.split('_') )
    elif string.count('_') == 1:
        color, outer_label = tuple( string.split('_') )
    else:
        color = string

    if color == 't':
        color = 'l'
        inner_label = outer_label
        outer_label = ''
    if color == 'i':
    	color = 'lc'
    	inner_label = outer_label
    	outer_label = ''
    elif color == 'x':
        color = 'l'
        inner_label = '$\\times$'
    elif color.isdigit():
        inner_label = color
        color = 'lc'
    elif color == '...':
        inner_label = '$\\cdot \\cdot \\cdot$'
        color = 'l'

    return (color, inner_label, outer_label, label_direction)

def generate_forest(string):

    #log = open("log.txt", "w")

    if len(string) == 0:
        return "\emptyset"

    level = 0
    forest = Forest()

    cache = ''
    level = 0
    current_node = None
    current_stolon = None
    new_node = None
    new_stolon = None
    for c in string + ',':
        # create new node
        if c in ['[', ',', '=', ']', '(', ')']:
            if c == '(':
                new_node = Cycle()

            elif cache != '':
                color, inner_label, outer_label, label_direction = decode_node_info(cache)
                cache = ''

                new_node = Node(
                                color = color, 
                                inner_label = inner_label, 
                                outer_label = outer_label, 
                                label_direction = label_direction,
                            )

            if new_node is not None:
                if level == 0:
                    forest.append(new_node)
                else:
                    current_node.add_child(new_node)

                if c in ['[', '(']:
                    level += 1
                    current_node = new_node

                new_node = None

            if c == '=':
                if current_stolon is None:
                    forest.stolons.append(Stolon(nodes = [forest.nodes[-1]]))
                    current_stolon = forest.stolons[-1]
                else:
                    current_stolon.append(forest.nodes[-1])
            elif c == ',' and level == 0 and current_stolon is not None:
                current_stolon.append(forest.nodes[-1])
                current_stolon = None
            elif c in [']', ')']:
                level -= 1
                current_node = current_node.parent

            continue

        cache += c

    forest.optimize()

    #log.close()

    return forest
