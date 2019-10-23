
#include "parser.hh"

int main()
{
    std::string s = "2 + -3^x - 2*(3*y - -4*z^g^u)";

    auto tree = parse<std::string::const_iterator, ast::calculator_grammar>(s.begin(), s.end());


}
