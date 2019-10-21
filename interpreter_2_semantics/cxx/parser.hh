#pragma once

#include <boost/config/warning_disable.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/variant/recursive_variant.hpp>
#include <boost/foreach.hpp>

#include <iostream>
#include <fstream>
#include <string>
#include <vector>


namespace client
{
    namespace fusion = boost::fusion;
    namespace phoenix = boost::phoenix;
    namespace qi = boost::spirit::qi;
    namespace ascii = boost::spirit::ascii;

    struct ast_tree;

    typedef
        boost::variant<
            boost::recursive_wrapper<ast_tree>,  // subtree
            std::string,                         // or value in leaf node
            double
        >
    ast_node;

    struct ast_tree
    {
        std::string name = "default";                      // tag name
        std::vector<ast_node> children;        // children
    };
}

BOOST_FUSION_ADAPT_STRUCT(
    client::ast_tree,
    (std::string, name)
    (std::vector<client::ast_node>, children)
)

namespace client
{
    int const tabsize = 4;

    void tab(int indent)
    {
        for (int i = 0; i < indent; ++i)
            std::cout << ' ';
    }

    struct ast_tree_printer
    {
        ast_tree_printer(int indent = 0)
          : indent(indent)
        {
        }

        void operator()(ast_tree const& ast) const;

        int indent;
    };

    struct ast_node_printer : boost::static_visitor<>
    {
        ast_node_printer(int indent = 0)
          : indent(indent)
        {
        }

        void operator()(ast_tree const& ast) const
        {
            ast_tree_printer(indent+tabsize)(ast);
        }

        void operator()(std::string const& value) const
        {
            std::cout << "  \"" << value << '"';
        }

        void operator()(double value) const
        {
            std::cout << "  \"" << value << '"';
        }

        int indent;
    };

    void ast_tree_printer::operator()(ast_tree const& ast) const
    {
        std::cout << std::endl;
        tab(indent);
        std::cout << ast.name;
        
        BOOST_FOREACH(ast_node const& node, ast.children)
        {
            boost::apply_visitor(ast_node_printer(indent), node);
        }

    }


    template <typename Iterator>
    struct calculator_grammar
      : qi::grammar<Iterator, ast_tree(), ascii::space_type>
    {
        calculator_grammar()
          : calculator_grammar::base_type(sum)
        {
            using qi::lit;
            using qi::lexeme;
            using qi::raw;
            using ascii::char_;
            using ascii::alnum;
            using ascii::alpha;
            using ascii::digit;
            using qi::double_;
            using qi::real_parser;
            using ascii::string;
            using namespace qi::labels;
            using phoenix::at_c;
            using phoenix::push_back;
            using qi::debug;

            CNAME %= raw[lexeme[alpha >> *(alnum | '_')]];
            NUMBER %= double_;

            number = NUMBER                             [at_c<0>(_val) = "number", push_back(at_c<1>(_val), _1)];
            const_ref = CNAME                           [at_c<0>(_val) = "const", push_back(at_c<1>(_val), _1)];

            value = number                              [_val = _1]
                | const_ref                             [_val = _1]
                | '(' >> sum                            [_val = _1]
                      >> ')';

            pow = value                                 [push_back(at_c<1>(_val), _1)]
                  >> '^' >> pow                         [at_c<0>(_val) = "pow", push_back(at_c<1>(_val), _1)]
                | value                                 [_val = _1];

            neg = '-' >> pow                            [at_c<0>(_val) = "neg", push_back(at_c<1>(_val), _1)]
                | pow                                   [_val = _1];

            product = neg                               [push_back(at_c<1>(_val), _1)]
                >>
                (   ('*' >> product                     [at_c<0>(_val) = "mul", push_back(at_c<1>(_val), _1)]  )
                  | ('/' >> product                     [at_c<0>(_val) = "div", push_back(at_c<1>(_val), _1)]  )
                )
                | neg                                   [_val = _1];

            sum = product                               [push_back(at_c<1>(_val), _1)]
                >>
                (   ('+' >> sum                         [at_c<0>(_val) = "add", push_back(at_c<1>(_val), _1)]  )
                  | ('-' >> sum                         [at_c<0>(_val) = "sub", push_back(at_c<1>(_val), _1)]  )
                )
                | product                               [_val = _1];

            /*
            sum.name("sum");
            product.name("product");
            neg.name("neg");
            pow.name("pow");
            value.name("value");
            number.name("number");
            const_ref.name("const");


            debug(number);
            debug(const_ref);
            debug(value);
            debug(pow);
            debug(neg);
            debug(product);
            debug(sum);
            */

        }

        qi::rule<Iterator, std::string(), ascii::space_type> CNAME;
        qi::rule<Iterator, double, ascii::space_type> NUMBER;

        qi::rule<Iterator, ast_tree(), ascii::space_type> number;
        qi::rule<Iterator, ast_tree(), ascii::space_type> const_ref;

        qi::rule<Iterator, ast_tree(), ascii::space_type> value;

        qi::rule<Iterator, ast_tree(), ascii::space_type> pow;

        qi::rule<Iterator, ast_tree(), ascii::space_type> neg;

        qi::rule<Iterator, ast_tree(), ascii::space_type> product;

        qi::rule<Iterator, ast_tree(), ascii::space_type> sum;

    };
}


