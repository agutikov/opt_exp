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
            std::string                          // or value in leaf node
        >
    ast_node;

    struct ast_tree
    {
        std::string name;                      // tag name
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
    int const tabsize = 2;

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
            tab(indent+tabsize);
            std::cout << "value: \"" << value << '"' << std::endl;
        }

        int indent;
    };

    void ast_tree_printer::operator()(ast_tree const& ast) const
    {
        tab(indent);
        std::cout << "tag: " << ast.name << std::endl;
        tab(indent);
        std::cout << '{' << std::endl;

        BOOST_FOREACH(ast_node const& node, ast.children)
        {
            boost::apply_visitor(ast_node_printer(indent), node);
        }

        tab(indent);
        std::cout << '}' << std::endl;
    }


    template <typename Iterator>
    struct calculator_grammar
      : qi::grammar<Iterator, ast_tree(), ascii::space_type>
    {
        calculator_grammar()
          : calculator_grammar::base_type(ast)
        {
            using qi::lit;
            using qi::lexeme;
            using ascii::char_;
            using boost::spirit::double_;
            using ascii::string;
            using namespace qi::labels;

            const_ref = string(_r1)         [_val += _1]];
            number = double_                [_val += _1];;
/*
            value = number | const_ref | '(' >> sum >> ')';

            pow = value >> '^' >> pow;

            pow_val = value | pow;

            neg = '-' >> pow_val;

            neg_val = pow_val | neg;

            mul = neg_val >> '*' >> product;
            div = neg_val >> '/' >> product;

            product = neg_val | div | mul;

            add = product >> '+' >> sum;
            sub = product >> '-' >> sum;

            sum = product | add | sub;

            ast = sum;
            */
            ast = *(const_ref | number)     [push_back(at_c<1>(_val), _1)];
        }

        qi::rule<Iterator, ast_tree(), ascii::space_type> ast;
/*
        qi::rule<Iterator, ast_tree(), ascii::space_type> sum;
        qi::rule<Iterator, ast_tree(), ascii::space_type> sub;
        qi::rule<Iterator, ast_tree(), ascii::space_type> add;

        qi::rule<Iterator, ast_tree(), ascii::space_type> product;
        qi::rule<Iterator, ast_tree(), ascii::space_type> div;
        qi::rule<Iterator, ast_tree(), ascii::space_type> mul;

        qi::rule<Iterator, ast_tree(), ascii::space_type> neg_val;
        qi::rule<Iterator, ast_tree(), ascii::space_type> neg;
        qi::rule<Iterator, ast_tree(), ascii::space_type> pow_val;
        qi::rule<Iterator, ast_tree(), ascii::space_type> pow;
        qi::rule<Iterator, ast_tree(), ascii::space_type> value;
*/
        qi::rule<Iterator, std::string(), ascii::space_type> const_ref;
        qi::rule<Iterator, std::string(), ascii::space_type> number;

    };
    //]
}


