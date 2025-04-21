prog ::= <declarations>
declarations ::= <list(<actor>)>
actor ::= "Actor" <symbol> { <state> <initialiser> <message-handler> }
expr ::= <number> | <string> | <symbol> | <bool> | <actor-reference> | ( <expr> ) | <expr> <infix> <expr>
actor-reference ::= '&' <symbol>
string ::= '"' [^"]* '"''
number ::= [-]?[0-9]*[.]?[0-9]*
infix ::= '+' | '*' | '-' | '/' | '^' | "==" | "<=" | ">=" | '<' | '>' | "&&" | "||"
bool ::= "true" | "false" | "not(" <expr> ')'
symbol ::= [a-zA-Z]^[{}"(),;]*
state ::= <list(<symbol> ';')>
initialiser ::= "Initialiser:" '{' <list(<statement>)> '}'
arg-list = <symbol> <arg-tail>
arg-tail ::= ',' <arg-list> | ε
statement ::= <statement-body> ';' 
statement-body ::= <assignment> | <return> | <actor> | <send> | <if-statement>
message-handler ::= "Update:" '(' <symbol> ')' '{' <list(<statement>)> '}'
assignment ::= <symbol> '=' <expr>
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

