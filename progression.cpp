#include "spotparser.h"
#include "progression.h"

#include <spot/tl/formula.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/relabel.hh>


#include <string>
#include <cstdio>
#include <iostream> 
#include <sstream>

#include <fstream>

// taken fron Shufang spotparser.cpp
//formula parse_formula(string filename)
//{
//    std::ifstream in(filename);
//    std::string line;
//    std::getline(in, line);
//    const char* ltl_str = line.c_str();
//    auto pf1 = spot::parse_infix_psl(ltl_str);
//	if (pf1.format_errors(std::cerr))
//	{
//        std::string f(ltl_str);
//		std::cerr << "Error LTL formula: " << f << std::endl;
//		exit(-1);
//	}
//	return res;
//}

std::vector<std::string> get_props(formula &f){
    std::vector<std::string> names;
    if (f.is_leaf()){
        std::string name = f.ap_name();
        if (std::find(names.begin(), names.end(), name) == names.end()) {
            names.push_back(name);
        }
    }else{
        for (formula child : f)
        {
            std::vector<std::string> child_names =  get_props(child);
            for(auto name : child_names){
                if (std::find(names.begin(), names.end(), name) == names.end()) {
                    names.push_back(name);
                }
            }
        }
    }
    return names;
}

//
//// get negation normal form of a formula
//formula get_nnf(formula &f)
//{
//  formula res;
//  if (f.kind() == op::ap || f.kind() == op::tt || f.kind() == op::ff)
//  {
//    res = f;
//  }
//  else
//  {
//    formula l = f[0], r, lft, rgt, res2;
//    formula lt, rt;
//    std::vector<formula> lst;
//    switch (f.kind())
//    {
//    case op::Not:
//      res = push_not_in(l);
//      break;
//    // Next
//    // X p = !(X !p)
//    case op::X:
//      r = get_nnf(l);
//      res = formula::unop(op::X, r);
//      break;
//    case op::G:
//      r = get_nnf(l);
//      res = formula::unop(op::G, r);
//      break;
//    case op::F:
//      r = get_nnf(l);
//      res = formula::unop(op::F, r);
//      break;
//     case op::U:
//      r = f[1];
//      lft = get_nnf(l);
//      rgt = get_nnf(r);
//      res = formula::U(lft, rgt);
//      break;
//    // weak Until
//    // φ W ψ ≡ (φ U ψ) ∨ G φ ≡ φ U (ψ ∨ G φ) ≡ ψ R (ψ ∨ φ)
//    // p W q = G p | (p U q) = (! F !p ) | (p U q)
//    case op::W:
//      r = f[1];
//      l = get_nnf(l);
//      r = get_nnf(r);
//      // res2 = ! p;
//      res2 = formula::multop(op::Or, {l, r});
//      res = formula::R(r, res2);
//      break;
//    case op::R:
//      r = f[1];
//      lft = get_nnf(l);
//      rgt = get_nnf(r);
//      res = formula::R(lft, rgt);
//      break;
//    case op::And:
//      for (formula child : f)
//      {
//        l = get_nnf(child);
//        lst.push_back(l);
//      }
//      res = formula::multop(op::And, lst);
//      break;
//          case op::Or:
//      for (formula child : f)
//      {
//        l = get_nnf(child);
//        lst.push_back(l);
//      }
//      res = formula::multop(op::Or, lst);
//      break;
//    case op::Implies:
//      r = f[1];
//      lft = formula::Not(l);
//      rgt = formula::multop(op::Or, {lft, r});
//      res = get_nnf(rgt);
//      break;
//    case op::Equiv:
//      // a <-> b = (a->b) & (b->a)
//      r = f[1];
//      lt = formula::binop(op::Implies, l, r);
//      lft = get_nnf(lt);
//      rt = formula::binop(op::Implies, r, l);
//      rgt = get_nnf(rt);
//      res = formula::multop(op::And, {lft, rgt});
//      break;
//    default:
//      cerr << "Formula: " << f << ". ";
//      throw runtime_error("Error formula in get_nnf()");
//      exit(-1);
//    }
//  }
//  return res;
//}
//
//// get progression of a formula given an interpretation
formula progr(formula &f, map<formula, formula>* m)
{
    formula res;
    if (f.kind() == op::tt || f.kind() == op::ff)
    {
        res = f; //make copy?
    }
    else
    {
        formula l = f.size() > 0 ? f[0] : formula();
        formula r, lft, rgt, res2;
        formula lt, rt;
        std::vector<formula> lst;

//        formula l = f[0], r, lft, rgt, res2;
//        formula lt, rt;
//        std::vector<formula> lst;
        switch (f.kind())
        {
            case op::ap:
                res = (*m)[f];
                break;
            case op::Not:
                r = progr(l, m);
                res = formula::unop(op::Not, r);
                break;
                // Next
                // X p = !(X !p)
            case op::X:
                res = l;  // copy?
                break;
            case op::G:
                lft = progr(l, m);
                res = formula::multop(op::And, {lft, f});  //copy f?
                break;
            case op::F:
                lft = progr(l, m);
                res = formula::multop(op::Or, {lft, f});  //copy f?
                break;
            case op::U:
                if (f.size() < 2) throw runtime_error("Error: U operator requires two children");
                r = f[1];
                lft = progr(l, m);
                rgt = progr(r, m);
                res2 = formula::multop(op::And, {lft,f});   //copy f?
                res = formula::multop(op::Or, {rgt, res2});
                break;
                // weak Until
                // φ W ψ ≡ (φ U ψ) ∨ G φ ≡ φ U (ψ ∨ G φ) ≡ ψ R (ψ ∨ φ)
                // p W q = G p | (p U q) = (! F !p ) | (p U q)
            case op::W:
                if (f.size() < 2) throw runtime_error("Error: W operator requires two children");
                r = f[1];
                res2 = formula::R(l, formula::multop(op::Or, {l, r}));
                res = progr(res2, m);
                break;
            case op::R:
                if (f.size() < 2) throw runtime_error("Error: R operator requires two children");
                r = f[1];
                lft = progr(l, m);
                rgt = progr(r, m);
                res2 = formula::multop(op::Or, {lft,l});   //copy f?
                res = formula::multop(op::And, {rgt, res2});
                break;
            case op::And:
                for (formula child : f)
                {
                    l = progr(child, m);
                    lst.push_back(l);
                }
                res = formula::multop(op::And, lst);
                break;
            case op::Or:
                for (formula child : f)
                {
                    l = progr(child, m);
                    lst.push_back(l);
                }
                res = formula::multop(op::Or, lst);
                break;
            case op::Implies:
                if (f.size() < 2) throw runtime_error("Error: Implies operator requires two children");
                r = f[1];
                lft = formula::Not(l);
                rgt = formula::multop(op::Or, {lft, r});
                res = progr(rgt, m);
                break;
            case op::Equiv:
                // a <-> b = (a->b) & (b->a)
                if (f.size() < 2) throw runtime_error("Error: Equiv operator requires two children");
                r = f[1];
                lt = formula::binop(op::Implies, l, r);
                lft = progr(lt, m);
                rt = formula::binop(op::Implies, r, l);
                rgt = progr(rt, m);
                res = formula::multop(op::And, {lft, rgt});
                break;
                //do we need to handle more opertator e.g. weak-next ??
            default:
                cerr << "Formula: " << f << ". ";
                throw runtime_error("Error formula in get_nnf()");
                exit(-1);
        }
    }
    // do boolean simplifications for tt & ff ??
//    res = simplify(res);
    return res;
}
//
//int main(char** args, int argv)
//{
//   char* ltl_str = " (a W b ) && G c && b R d && (a U b)";
//   formula f = parse_formula(ltl_str);
//   cout << "formula: " << f << endl;
//   return 0;
//}
