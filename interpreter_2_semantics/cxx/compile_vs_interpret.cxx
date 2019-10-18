
#include <cstdio>
#include <functional>
#include <map>
#include <string>
#include <any>
#include "parser.hh"

// WOW! Is it possible?
auto id = [](auto x){ return x; };

template<typename T, typename ...Targs>
auto value_closure(T x)
{
    return [x](Targs... xs){ return x; };
}


/*
    Possibly it will be hard to implement multi-parameter lambda,
    so let's try to pass parameters as vector or tuple of std::any.
*/


/*============================================================================================
 * 
 * 
 *============================================================================================
 */

typedef std::map<std::string, std::any> env_t;

typedef std::function<std::any(const env_t&)> compiled_f;

typedef std::function<compiled_f(const compile_ops_t&, const std::string&)> compilation_f;

typedef std::map<std::string, compilation_f> compile_ops_t;

auto compile_tree(const compile_ops_t& ops, const std::string& tree)
{
    return ops.find(tree)->second(ops, tree);
}













/*============================================================================================
 * 
 * 
 *============================================================================================
 */



int main()
{
    auto f1 = value_closure<int, env_t>(100);
    auto f2 = value_closure<float, env_t>(200.0);
    auto f3 = value_closure<const char*, env_t>("300");

    env_t env = {{"x", 'a'}, {"y", 'b'}, {"z", 'c'}, {"X", 'd'}};

    printf("%f %s %d\n", f2(env), f3(env), f1(env));


    return 0;
}














