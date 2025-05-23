import os
import argparse
import sys
from typing import Callable, List, Tuple, Optional, Dict
from dataclasses import dataclass
from trs_parser import TRSParser, parse_trs_file, Term, Rule
from tqdm import tqdm

@dataclass
class Position:
    """Represents a position in a term as a list of indices."""
    indices: List[int]

    def __str__(self) -> str:
        if not self.indices:
            return "ε"
        return ".".join(str(i) for i in self.indices)

    def is_prefix_of(self, other: 'Position') -> bool:
        """Check if this position is a prefix of another position."""
        if len(self.indices) > len(other.indices):
            return False
        return self.indices == other.indices[:len(self.indices)]

    def append(self, index: int) -> 'Position':
        """Create a new position by appending an index."""
        return Position(self.indices + [index])

def get_positions(term: Term) -> List[Position]:
    """Get all positions in a term where a subterm occurs."""
    positions = [Position([])]  # Root position
    
    def collect_positions(t: Term, pos: Position):
        for i, arg in enumerate(t.args):
            if arg.is_variable:
                continue
            new_pos = pos.append(i)
            positions.append(new_pos)
            collect_positions(arg, new_pos)
    
    collect_positions(term, Position([]))
    # print("Term: ", term, "Positions: ", positions)
    return positions

def get_subterm_at(term: Term, pos: Position) -> Term:
    """Get the subterm at a given position."""
    current = term
    for idx in pos.indices:
        if not current.args or idx >= len(current.args):
            raise ValueError(f"Invalid position {pos} in term {term}")
        current = current.args[idx]
    return current

def replace_subterm_at(term: Term, pos: Position, new_term: Term) -> Term:
    """Replace the subterm at a given position with a new term."""
    if not pos.indices:
        return new_term
    
    new_args = list(term.args)  # Create a copy of the arguments
    current_pos = pos.indices[0]
    if current_pos >= len(new_args):
        raise ValueError(f"Invalid position {pos} in term {term}")
    
    if len(pos.indices) == 1:
        new_args[current_pos] = new_term
    else:
        new_args[current_pos] = replace_subterm_at(
            new_args[current_pos], 
            Position(pos.indices[1:]), 
            new_term
        )
    
    return Term.function(term.name, new_args)

def unify(term1: Term, term2: Term) -> Optional[Dict[str, Term]]:
    """Try to unify two terms, returning a substitution if possible."""
    if term1.is_variable:
        # If term1 is a variable, it can unify with anything
        return {term1.name: term2}
    if term2.is_variable:
        # If term2 is a variable, it can unify with anything
        return {term2.name: term1}
    if term1.name != term2.name or len(term1.args) != len(term2.args):
        # Different function symbols or arities can't unify
        return None
    
    # Try to unify all arguments
    substitution = {}
    for arg1, arg2 in zip(term1.args, term2.args):
        sub = unify(arg1, arg2)
        if sub is None:
            return None
        # Merge substitutions, checking for conflicts
        for var, term in sub.items():
            if var in substitution:
                if substitution[var] != term:
                    return None
            else:
                substitution[var] = term
    return substitution

def apply_substitution(term: Term, substitution: Dict[str, Term]) -> Term:
    """Apply a substitution to a term."""
    if term.is_variable:
        return substitution.get(term.name, term)
    return Term.function(
        term.name,
        [apply_substitution(arg, substitution) for arg in term.args]
    )
    
def compute_critical_terms(term1: Term, term2: Term) -> List[Tuple[Term, Term]]:
    """Compute all non-trivial critical pairs between two terms."""
    critical_terms = []
    
    # Get all positions in term1 (skipping variables)
    positions = get_positions(term1)
    
    for pos in positions:
        # Skip the root position as it would lead to trivial overlaps
        if not pos.indices:
            continue
            
        subterm = get_subterm_at(term1, pos)
        # Try to unify term2 with the subterm
        substitution = unify(term2, subterm)
        
        if substitution is not None:
            term1_subst = apply_substitution(term1, substitution)
            critical_terms.append(term1_subst)
    return critical_terms

def compute_critical_pairs(rule1: Rule, rule2: Rule) -> List[Tuple[Term, Term]]:
    """Compute all non-trivial critical pairs between two rules."""
    critical_pairs = []
    
    # Get all positions in rule1's left side where rule2's left side might match
    positions = get_positions(rule1.left)
    
    for pos in positions:
        # Skip the root position as it would lead to trivial overlaps
        if not pos.indices:
            continue
            
        subterm = get_subterm_at(rule1.left, pos)
        # Try to unify rule2's left side with the subterm
        substitution = unify(rule2.left, subterm)
        
        if substitution is not None:
            # Apply the substitution to both rules
            rule1_left = apply_substitution(rule1.left, substitution)
            rule1_right = apply_substitution(rule1.right, substitution)
            rule2_right = apply_substitution(rule2.right, substitution)
            
            # Replace the subterm in rule1's right side with rule2's right side
            result1 = replace_subterm_at(rule1_right, pos, rule2_right)
            
            # The critical pair is (result1, rule2_right)
            if result1 != rule2_right:  # Only add non-trivial pairs
                critical_pairs.append((result1, rule2_right))
    
    return critical_pairs


def rename_vars(term: Term, name_transform: Callable[[str], str]) -> Term:
    """Rename variables in a term with a given prefix."""
    if term.is_variable:
        return Term.variable(name_transform(term.name))
    return Term.function(term.name, [rename_vars(arg, name_transform) for arg in term.args])
                
def find_connected_components(adjacency_list: Dict[int, List[int]]) -> List[List[int]]:
    """Find all connected components in an undirected graph using DFS."""
    visited = set()
    components = []
    
    def dfs(node: int, component: List[int]):
        visited.add(node)
        component.append(node)
        for neighbor in adjacency_list[node]:
            if neighbor not in visited:
                dfs(neighbor, component)
    
    for node in adjacency_list:
        if node not in visited:
            component = []
            dfs(node, component)
            components.append(component)
    
    return components

def overlap(t1: Term, t2: Term) -> bool:
    """Check if two terms overlap."""
    # assume t1 and t2 are renamed
    return compute_critical_terms(t1, t2) != [] or compute_critical_terms(t2, t1) != []

def overlap_rules(r1: Rule, r2: Rule) -> bool:
    """Check if two rules overlap."""
    return overlap(r1.left, r2.left) or overlap(r1.left, r2.right) or overlap(r1.right, r2.left) or overlap(r1.right, r2.right)
    
def build_rule_graph(rules: List[Rule]) -> Dict[int, List[int]]:
    """Build an undirected graph where nodes are rules and edges are overlaps."""
    # First rename variables in all rules to avoid conflicts
    for i, rule in enumerate(rules):
        left = rename_vars(rule.left, lambda x: x + "_" + str(i))
        right = rename_vars(rule.right, lambda x: x + "_" + str(i))
        rules[i] = Rule(left, right)
    
    # Build adjacency list
    adjacency_list = {i: [] for i in range(len(rules))}
    
    # Check each pair of rules for overlaps
    for i in range(len(rules)):
        for j in range(i + 1, len(rules)):
            if overlap_rules(rules[i], rules[j]):
                adjacency_list[i].append(j)
                adjacency_list[j].append(i)
    
    return adjacency_list


def test():
    # M(M(x,y),z)
    t1 = Term.function("M", [Term.function("M", [Term.variable("x"), Term.variable("y")]), Term.variable("z")])
    # M(I(x),x)
    t2 = Term.function("M", [Term.function("I", [Term.variable("x")]), Term.variable("x")])
    # M(E,z) = z
    t3 = Term.function("M", [Term.function("E"), Term.variable("z")])
    
    t1 = rename_vars(t1, lambda x: x + "1")
    t2 = rename_vars(t2, lambda x: x + "2")
    t3 = rename_vars(t3, lambda x: x + "3")
    
    print(t1)
    print(t2)
    terms = compute_critical_terms(t1, t2)
    terms += compute_critical_terms(t2, t1)
    print()
    for t in terms:
        print(t)
            
            
def main():
    """Find critical pairs in TRS files."""
    parser = argparse.ArgumentParser(description='Find critical pairs in TRS files')
    parser.add_argument('--debug', action='store_true', help='Enable debug output')
    args = parser.parse_args()
    
    trs_dir = "mkbTT"
    trs_files = []
    for filename in os.listdir(trs_dir):
        if filename.endswith(".trs"):
            filepath = os.path.join(trs_dir, filename)
            trs_files.append((filename,filepath))
            
    connected_components = {}
    for filename, filepath in tqdm(trs_files):
        try:
            _, rules = parse_trs_file(filepath, debug=args.debug)
            
            # Build graph and find components
            graph = build_rule_graph(rules)
            components = find_connected_components(graph)
            
            # Sort component sizes in descending order
            component_sizes = sorted([len(comp) for comp in components], reverse=True)
            connected_components[filename] = component_sizes
            
        except Exception as e:
            print(f"Error analyzing {filename}: {e}")
            exit(1)
                
    for filename, component_sizes in sorted(connected_components.items(), key=lambda x: x[1][0], reverse=False):
        print(f"{filename}: {component_sizes}")

if __name__ == "__main__":
    main()

"""
General idea:
we can complete each connected component individually with KBC

However, usually all rules are in one connected component
And if not, KBC would handle it on its own quite well
"""