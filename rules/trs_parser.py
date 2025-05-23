from dataclasses import dataclass
from typing import List, Set
import sys

@dataclass
class Term:
    """Represents a term in a TRS file. Can be a variable, constant, or function application."""
    name: str
    args: List['Term'] = None
    is_variable: bool = False

    def __post_init__(self):
        if self.args is None:
            self.args = []

    def __str__(self) -> str:
        if self.is_variable:
            return "?" + self.name
        if not self.args:
            return self.name
        return f"{self.name}({', '.join(str(arg) for arg in self.args)})"

    @classmethod
    def variable(cls, name: str) -> 'Term':
        """Create a variable term."""
        return cls(name=name, is_variable=True)

    @classmethod
    def function(cls, name: str, args: List['Term'] = None) -> 'Term':
        """Create a function term (constant if args is empty)."""
        return cls(name=name, args=args or [], is_variable=False)

@dataclass
class Rule:
    """Represents a rewrite rule in a TRS file."""
    left: Term
    right: Term

    def __str__(self) -> str:
        return f"{self.left} -> {self.right}"

class TRSParser:
    """Parser for TRS files."""
    
    def __init__(self, debug: bool = False):
        self.variables: Set[str] = set()
        self.rules: List[Rule] = []
        self.current_pos = 0
        self.content = ""
        self.debug = debug

    def _debug_print(self, *args, **kwargs):
        """Print debug messages if debug mode is enabled."""
        if self.debug:
            print(*args, file=sys.stderr, **kwargs)

    def parse_file(self, filepath: str) -> tuple[Set[str], List[Rule]]:
        """Parse a TRS file and return its variables and rules."""
        with open(filepath, 'r') as f:
            self.content = f.read()
        self.current_pos = 0
        self.variables = set()
        self.rules = []
        
        self._debug_print(f"Parsing file: {filepath}")
        
        # Parse VAR section
        self._skip_whitespace()
        if not self._match("(VAR"):
            raise ValueError("Expected (VAR at start of file")
        self._parse_vars()
        if not self._match(")"):
            raise ValueError("Expected ) after VAR section")
            
        # Parse RULES section
        self._skip_whitespace()
        if not self._match("(RULES"):
            raise ValueError("Expected (RULES after VAR section")
        self._parse_rules()
        if not self._match(")"):
            raise ValueError("Expected ) after RULES section")
            
        return self.variables, self.rules

    def _skip_whitespace(self):
        """Skip whitespace and comments in the input."""
        while self.current_pos < len(self.content):
            if self.content[self.current_pos].isspace():
                self.current_pos += 1
            elif self.content[self.current_pos:self.current_pos+2] == "(*":
                # Skip comments
                while (self.current_pos < len(self.content) - 1 and 
                       self.content[self.current_pos:self.current_pos+2] != "*)"):
                    self.current_pos += 1
                self.current_pos += 2
            else:
                break

    def _match(self, expected: str) -> bool:
        """Try to match the expected string at current position."""
        if self.content[self.current_pos:self.current_pos + len(expected)] == expected:
            self.current_pos += len(expected)
            return True
        return False

    def _parse_vars(self):
        """Parse the variables section."""
        self._skip_whitespace()
        while self.current_pos < len(self.content):
            if self.content[self.current_pos] == ')':
                break
            var = self._parse_identifier()
            self.variables.add(var)
            self._skip_whitespace()

    def _parse_identifier(self) -> str:
        """Parse an identifier (variable or function name)."""
        start = self.current_pos
        # Allow any non-whitespace character that's not a parenthesis or comma
        while (self.current_pos < len(self.content) and 
               not self.content[self.current_pos].isspace() and
               self.content[self.current_pos] not in '(),'):
            self.current_pos += 1
        return self.content[start:self.current_pos]

    def _parse_term(self) -> Term:
        """Parse a term (variable, constant, or function application)."""
        self._skip_whitespace()
        name = self._parse_identifier()
        
        # Debug output
        self._debug_print(f"Parsing term, found name: '{name}' at pos {self.current_pos}")
        
        # Check if it's a variable
        if name in self.variables:
            return Term.variable(name)
        
        # Check if it's a function application
        if self.current_pos < len(self.content) and self.content[self.current_pos] == '(':
            self.current_pos += 1  # Skip '('
            args = []
            while True:
                self._skip_whitespace()
                if self.content[self.current_pos] == ')':
                    self.current_pos += 1
                    break
                args.append(self._parse_term())
                self._skip_whitespace()
                if self.content[self.current_pos] == ',':
                    self.current_pos += 1
                elif self.content[self.current_pos] == ')':
                    self.current_pos += 1
                    break
            return Term.function(name, args)
        return Term.function(name)

    def _parse_rules(self):
        """Parse the rules section."""
        while self.current_pos < len(self.content):
            self._skip_whitespace()
            if self.content[self.current_pos] == ')':
                break
                
            self._debug_print(f"Starting to parse rule at pos {self.current_pos}")
            left = self._parse_term()
            self._debug_print(f"Parsed left side: {left}")
            self._skip_whitespace()
            
            if not self._match("->"):
                raise ValueError(f"Expected -> in rule at position {self.current_pos}, found: {self.content[self.current_pos:self.current_pos+10]}")
                
            right = self._parse_term()
            self._debug_print(f"Parsed right side: {right}")
            self._skip_whitespace()
            
            self.rules.append(Rule(left, right))

def parse_trs_file(filepath: str, debug: bool = False) -> tuple[Set[str], List[Rule]]:
    """Parse a TRS file and return its variables and rules.
    
    Args:
        filepath: Path to the TRS file
        debug: If True, print debug information to stderr
    """
    parser = TRSParser(debug=debug)
    return parser.parse_file(filepath)
