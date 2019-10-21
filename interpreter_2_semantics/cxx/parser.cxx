
#include "parser.hh"

int main()
{
    std::string storage = "2 + -3^x - 2*(3*y - -4*z^g^u)";

    typedef client::calculator_grammar<std::string::const_iterator> calculator_grammar;
    calculator_grammar g;
    client::ast_tree tree;

    using boost::spirit::ascii::space;
    std::string::const_iterator iter = storage.begin();
    std::string::const_iterator end = storage.end();
    bool r = phrase_parse(iter, end, g, space, tree);

    if (r && iter == end) {
        client::ast_tree_printer printer;
        printer(tree);
        std::cout << std::endl;
        return 0;
    } else {
        std::string::const_iterator some = iter+30;
        std::string context(iter, (some>end)?end:some);
        std::cout << "stopped at: \"" << context << "\"\n";
        return 1;
    }
}
