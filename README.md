Language Interpretor

Purpose: Create an interpretor that parses and evaluates a program in a language called JILI. JILI is a simple, arithmetic language defined by the professors in CSC 430 (programming languages) at Cal Poly.

Contributors: Makayla Soh, Tarani Srikanth, Dani Lopez

Description:

Each file is an interpretor using different methods and for slightly different versions of JILI. Specific language descriptions are described at the top of the file.

PARSING

The program accepts the concrete JILI syntax which is essentially read as a string. The Racket language is a useful host langauge since the syntax is automatically broken down into a list of components. Using the "built-in" racket parsing, the program then has to decifer the components. Each component is wrapped in abstract syntax. This abstract syntax defines what the input is. Parsing is recursive as there may be an expression within an expression i.e. 1 + (2 + 2).

The abstract syntax is defined as expressions (ExprC) that can be identified. The ExprC depends on the specific languge implementation. Some possible expressions that are included:
- numbers
- binary operations: + - / *
- identifiers (variables)
- other operations: leq0?, if statements
- application of a function

In the environment and store versions of JILI, all operations get abstracted to applications of procedure. These procedures may be the binary operations (+, -, /, etc) or more advaced operations such as creating an array.

INTERPRETING

Interpreting is where the evaluation occurs. Given abstract syntax, the program can execute depending on the requested action. The abstract syntax allows for the action to be understood/interpreted. With just the concrete langauge, the host langauge does not understand the requested action. Interpreting is recursive as there may be an expression within an expression i.e. 1 + (2 + 2). Eagar evaluation is used. This means arguments are always evaluated before being passed into a function or larger expression. Interprting pimitive values is straight forward. For instance, an expression that is a number simply must return a number. An expression that is a string returns a string. However, if there is a function application then parameters and arguments must be accoutned for.

There are two main ways of interpreting function applications:

Substitution: This is where each argument is substituted directly for the corresponding identifier in each expression. The substitution is done as the first pass when evaluating a the function application. After all the arguments are correctly substituted in, then we can evalauate without any undefined variables. This causes two passes through the function.

Environment: The environment ensures scope while also allowing only a single pass through the function application. Each argument is applied only when the corresponding identifier is used. Thus each identifier with it's value is bound in the environemnt. When the identifier is used, the value it's bound to is looked up in the environment.
