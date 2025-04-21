prog ::= <declarations>
declarations ::= <list(<actor>)>
actor ::= "actor" <symbol> { <state> <initialiser> <message-handler> }
expr ::= <number> | <string> | <symbol> | <bool> | ( <expr> ) | <expr> <infix> <expr>
string ::= '"' [^"]* '"''
number ::= [-]?[0-9]*[.]?[0-9]*
infix ::= '+' | '*' | '-' | '/' | '^' | "==" | "<=" | ">=" | '<' | '>' | "&&" | "||"
bool ::= "true" | "false" | "not(" <expr> ')'
symbol ::= [a-zA-Z]^[{}"(),;]*
state ::= "state" <symbol> ':' <type-expr> ';'
initialiser ::= "initialiser" '{' <list(<statement>)> '}'
arg-list = <symbol> ':' <type-expr> <arg-tail>
arg-tail ::= ',' <arg-list> | ')'
statement ::= <statement-body> ';' 
statement-body ::= <assignment> | <return> | <actor> | <send> | <if-statement>
message-handler ::= "update" '(' <symbol> ':' <type-expr> ')' '{' <list(<statement>)> '}'
assignment ::= <symbol> ':' <type-expr> '=' <expr>
return ::= "return" <expr>
send ::= "send(" <expr> ',' <expr> ")"
if-statement ::= "if" <expr> '{' <list(<statement>)> '}' <if-tail>
if-tail ::= "else" '{' <list(<statement>)> '}' | ε
type-expr ::= <base> | <forall> | <constructor> | <typevar> | <actor>
base ::= [A-Z][a-zA-Z]+
forall ::= "forall(" <list(<typevar> ',')> ')' '.' <type-expr>
typevar ::= '\'' [a-z]+
actor ::= "Pid(" <type-expr> ')'
constructor ::= <base> '(' <list(<type-expr> ',')> ')'
