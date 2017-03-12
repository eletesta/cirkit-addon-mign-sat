/* CirKit: A circuit toolkit
 * Copyright (C) 2009-2015  University of Bremen
 * Copyright (C) 2015-2016  EPFL
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "mig_sat.hpp"

#include <iostream>
#include <cmath>
#include <memory>
#include <ctime>

#include <boost/dynamic_bitset.hpp>
#include <boost/format.hpp>
#include <boost/optional.hpp>

#include <classical/abc/abc_api.hpp>
#include <classical/abc/abc_manager.hpp>

#include <core/utils/range_utils.hpp>
#include <core/utils/timer.hpp>
#include <classical/mig_sat/spec_representation_mign.hpp>

#include <classical/mign/mign.hpp>
#include <classical/mign/mign_utils.hpp>
#include <classical/mign/mign_simulate.hpp>
#include <classical/mign/mign_invfree.hpp>

#include "sat/bsat/satSolver.h"

using namespace boost::assign;

using boost::format;
using boost::str;

namespace abc
{

sat_solver* sat_solver_new(); 
void sat_solver_setnvars(sat_solver* s,int n);
int Abc_Var2Lit( int x, int c );
void sat_solver_addclause( sat_solver* solver, int a, int b);
int sat_solver_solve(sat_solver* s, lit* begin, lit* end, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, ABC_INT64_T nConfLimitGlobal, ABC_INT64_T nInsLimitGlobal);
int sat_solver_var_value( sat_solver* solver, int i );
}

namespace cirkit
{
	
struct exact_inst
{
	
exact_inst( unsigned num_vars, bool verbose, unsigned n_output) :
      SpecVars ( num_vars ), 
	  eVerbose (verbose), 
	  SpecFunc (n_output)
    {
		Sat = NULL; 
		//SpecFunc = 1; 
		Rows = pow(2,SpecVars) - 1; // -1 eliminating the 000 normal 
		//std::cout << " input =" << SpecVars << std::endl; 
		//std::cout << " Rows = " << Rows << std::endl; 
    }
	
	
void tt_from_spec( tt func)
{
	tt_Spec.resize(1); // il resize in base al numero di output 
	tt_Spec[0] = func; 
}

void tt_from_spec( mign_graph mign)
{
	const mign_tt_simulator simulator{};
	auto values = simulate_mign(mign, simulator);
	tt_Spec.resize(1);
	auto one_output = mign.outputs(); 
	tt_Spec[0] = values[one_output[0].first];
}

void tt_from_spec_MO( mign_graph mign, std::vector<bool> normal_MO)
{
	const mign_tt_simulator simulator{};
	auto values = simulate_mign(mign, simulator);
	tt_Spec.resize(mign.outputs().size());
	auto one_output = mign.outputs(); 
	for ( auto x = 0; x < tt_Spec.size(); x++)
	{
         
		tt_Spec[x] = values[one_output[x].first];
		
		//std::cout <<tt_Spec[x] << std::endl;
		if (normal_MO[x] == 0)
		{
			tt_Spec[x].flip(); 
		}
		
	}
	
}

std::vector<std::pair<unsigned, unsigned>> tt_symmetric (tt spec)
{
    std::vector<std::pair<unsigned, unsigned>> symm_pairs;

    const auto n = tt_num_vars( spec );

    for ( auto j = 1u; j < n; ++j )
    {
      for ( auto i = 0u; i < j; ++i )
      {
        if ( tt_permute( spec, i, j ) == spec )
        {
          symm_pairs.push_back( {i, j} );
        }
      }
    }
	
	return symm_pairs; 
}

void create_var (int ngate, int maxdepth, int fanout)
{
	Noper = 16; 
    nGates      = ngate; // r 
    nSimVars    = nGates * Rows; // xit
	////std::cout << " nSimVar = " << nSimVars << std::endl; 
	nOutputVars = SpecFunc * nGates; 
    //nOutputVars = pSes->SpecFunc * nGates;
    nGateVars   = nGates * 7; // 7 combinations with 3 inputs
	////std::cout << " nGVar = " << nGateVars << std::endl; 
    nSelectVars = 0;
    for ( auto i = SpecVars; i < SpecVars + nGates; i++ )
          nSelectVars += ( i * ( i - 1 ) * (i - 2) ) / 6; // 6 = possible way of combinate 3 numbers ;) 
     ////std::cout << " nsel = " << nSelectVars << std::endl;
	nOutputOffset = nSimVars;
	nGateOffset   = nSimVars + nOutputVars;
	nSelectOffset = nSimVars + nOutputVars + nGateVars;
	   
    abc_manager::get();
    abc::Abc_FrameGetGlobalFrame();
     /* if we already have a SAT solver, then restart it (this saves a lot of time) */
    if ( Sat )
	   abc::sat_solver_restart( Sat );
    else
       Sat = abc::sat_solver_new();
	
	nOperVars = Noper * nGates; // to allow only majorities operations 
	nOperOffset = nSimVars + nOutputVars + nGateVars + nSelectVars; 
	
	MaxDepth = maxdepth; 
	MaxFanout = fanout; 
	nDepthVars = MaxDepth > 0 ? ( nGates * ( nGates + 1 ) ) / 2 : 0;
	nDepthOffset = nSimVars + nOutputVars + nGateVars + nSelectVars + nOperOffset; 
	//nOrdered_SelVars = nSelectVars;  // fan-out constraints 
	//nOrdered_SelOffset = nSimVars + nOutputVars + nGateVars + nSelectVars + nOperOffset + nDepthOffset; 
    abc::sat_solver_setnvars( Sat, nSimVars + nOutputVars + nGateVars + nSelectVars + nOperVars + nDepthVars);
	
	std::cout << " # of variables = " << nSimVars + nOutputVars + nGateVars + nSelectVars + nOperVars<< std::endl; 	   	
}

int SimVar( int i, int t )
{
	// no Offset for SImVar
    assert( i < nGates );
    assert( t < Rows );

    return Rows * i + t;
}

int GateVar( int i, int p, int q, int u )
{
	////std::cout << " i = " << i << " p = " << p << " q = " << q << std::endl; 
    assert( i < nGates );
    assert( p < 2 );
    assert( q < 2 );
	assert( u < 2); 
    assert( p > 0 || q > 0 || u > 0); // normal 

    return nGateOffset + i * 7 + ( p << 1 ) + 2*p + (q << 1) + u - 1;
}

int SelectVar( int i, int j, int k, int w )
{
	////std::cout << i << " " << j << " " << k << " " << w << std::endl; 
    int a;
    int offset;

    assert( i < nGates );
    assert( w < SpecVars + i );
    assert( j < k );
	assert( k < w );

    offset = nSelectOffset;
    for ( a = SpecVars; a < SpecVars + i; ++a ) // se i = 0 non entra 
        //offset += a * ( a - 1 ) / 2;
	    offset += a * (a-1) * (a-2) / 6; 
	////std::cout << " Offset " << offset << std::endl; 
	for (auto x = 0; x < j; x++)
	{
		offset = offset + ((SpecVars  + i -1 - x) * (SpecVars + i - 2 - x))/2;
	}

    return offset + ( -(k-j-1) * (  k -j- 2 * ( SpecVars - 1 + i -j ) ) ) / 2 + ( w - k - 1 ) ;
}

int OutputVar(  int h, int i )
{
    assert( h < SpecFunc );
    assert( i < nGates );

    return nOutputOffset + nGates * h + i;
}

int OperVar( int i, int g)
{
    assert( i < Noper);
    return nOperOffset +  i + g * Noper;
}

int DepthVar (int i, int l)  // dil
{
	assert( l >= 0 );
	assert( i < nGates );
    assert( l <= i );

	return nDepthOffset + ( ( i * ( i + 1 ) ) / 2 ) + l ;    // ho una di per ogni gate e poi ho un j  d11 d21 d22 
}


void create_main_clauses (int t, int i, int j, int k, int w, int a, int b, int c, int d) // names refer to the paper 
{
	
	int pLits[6], ctr = 0;

	pLits[ctr++] = abc::Abc_Var2Lit( SelectVar( i, j, k, w ), 1 ); 
    pLits[ctr++] = abc::Abc_Var2Lit( SimVar( i, t ), a );

	if ( j < SpecVars ) // if j <= n xjt is constant because they are pointing to PI
	    {
	        if ( ( ( ( t + 1 ) & ( 1 << j ) ) ? 1 : 0 ) != b )
	            return;
	    }
	else
	    pLits[ctr++] = abc::Abc_Var2Lit( SimVar(j - SpecVars, t ), b );

	if ( k < SpecVars ) // if k <= n xkt is constant 
	    {
	        if ( ( ( ( t + 1 ) & ( 1 << k ) ) ? 1 : 0 ) != c )
	            return;
	    }
	else
	    pLits[ctr++] = abc::Abc_Var2Lit( SimVar( k - SpecVars, t ), c );
	
	if ( w < SpecVars ) // if k <= n xkt is constant 
	    {
	        if ( ( ( ( t + 1 ) & ( 1 << w ) ) ? 1 : 0 ) != d )
	            return;
	    }
	else
	    pLits[ctr++] = abc::Abc_Var2Lit( SimVar( w - SpecVars, t ), d );
 
    if ( b > 0 || c > 0 || d > 0 ) // otherwise omitting the last term. Because 0 <=> 0 is 1, and 1 V something always = 1. 
	   {
	   	 pLits[ctr++] = abc::Abc_Var2Lit( GateVar(i, b, c , d), 1 - a );
	   }
	
	abc::sat_solver_addclause(Sat , pLits, pLits + ctr );
}

int Depthclause ()
{
    int i, j, k, w, l, d, h, jj, kk, ww;
    int pLits[3];

    for ( i = 0; i < nGates; ++i )
    {
        /* propagate depths from children */ 
		for ( w = 2; w < i; w++)   // for j = . to be done only if j > n . cosi j non predne un PI come input. allora ha senso fare questo. per sempio se gate = 4 (w = 3), allora j   puo prendere un altro nodo 
		     for ( k = 1; k < w; ++k )
		            for ( j = 0; j < k; ++j )
		            {
		                pLits[0] = abc::Abc_Var2Lit( SelectVar( i, SpecVars + j, SpecVars + k , SpecVars + w), 1 );
		                for ( jj = 0; jj <= j; ++jj )
		                {
							
		                    pLits[1] = abc::Abc_Var2Lit( DepthVar( j, jj ), 1 );
		                    pLits[2] = abc::Abc_Var2Lit( DepthVar( i, jj + 1 ), 0 );
		                    abc::sat_solver_addclause( Sat, pLits, pLits + 3 );
		                }
		            }
		
		for ( w = 1; w < i; ++w)
		     for ( k = 0; k < w; ++k ) // for k ==. to be done only if k > n
			      for ( j = 0; j < SpecVars + k; ++j )
					   {
					                pLits[0] = abc::Abc_Var2Lit( SelectVar( i, j, SpecVars + k, SpecVars + w ), 1 );
					                for ( kk = 0; kk <= k; ++kk )
					                {
					                    pLits[1] = abc::Abc_Var2Lit( DepthVar( k, kk ), 1 );
					                    pLits[2] = abc::Abc_Var2Lit( DepthVar( i, kk + 1 ), 0 );
					                    abc::sat_solver_addclause( Sat, pLits, pLits + 3 );
					                }
					    }
					
		for ( w = 0; w < i; ++w)
			for ( k = 0; k < SpecVars + w; ++k ) // for w ==. to be done only if k > n
				for ( j = 0; j < k; ++j )
					{
					pLits[0] = abc::Abc_Var2Lit( SelectVar( i, j, k, SpecVars + w ), 1 );
					for ( ww = 0; ww <= w; ++ww )
						{
						pLits[1] = abc::Abc_Var2Lit( DepthVar( w, ww ), 1 );
						pLits[2] = abc::Abc_Var2Lit( DepthVar( i, ww + 1 ), 0 );
						abc::sat_solver_addclause( Sat, pLits, pLits + 3 );
						}
					 }
      
         /* arrival times are 0 for inputs */
         pLits[0] = abc::Abc_Var2Lit( DepthVar( i, 0 ), 0 );
         abc::sat_solver_addclause( Sat, pLits, pLits + 1 );
        

        /* reverse order encoding of depth variables */
        for ( j = 1; j <= i; ++j )
        {
            pLits[0] = abc::Abc_Var2Lit( DepthVar(  i, j ), 1 );
            pLits[1] = abc::Abc_Var2Lit( DepthVar( i, j - 1 ), 0 );
            abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
        }

        /* constrain maximum depth */
        if ( MaxDepth <= i )
            for ( h = 0; h < SpecFunc; ++h )
            {
                pLits[0] = abc::Abc_Var2Lit( OutputVar( h, i ), 1 );
                pLits[1] = abc::Abc_Var2Lit( DepthVar( i, MaxDepth ), 1 );
                if ( !abc::sat_solver_addclause(Sat, pLits, pLits + 2 ) )
                    return 0;
            } 
    }

    return 1;
}

int ADD_FIXED_CLAUSES ()
{
	int pLits[1];
	int i = 0; 
	
	for ( i = 0; i < nGates; ++i )
	{
		if (i == 0)
		{
			
			  pLits[0] = abc::Abc_Var2Lit( SelectVar( i, 0,2,4), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 ); 
			  
			  pLits[0] = abc::Abc_Var2Lit( OperVar( 0,i), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 );
		}
		else if (i == 1)
		{
			
			  pLits[0] = abc::Abc_Var2Lit( SelectVar( i, 2,4,5), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 ); 
			  
			  pLits[0] = abc::Abc_Var2Lit( OperVar( 3,i ), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 );
		}
		
		else if (i == 2)
		{
			
			  pLits[0] = abc::Abc_Var2Lit( SelectVar( i, 0,5,6), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 ); 
			  
			  pLits[0] = abc::Abc_Var2Lit( OperVar( 2,i ), 0 );
			   abc::sat_solver_addclause(Sat, pLits, pLits + 1 );
		}
		else if (i == 3)
		{
			
			  pLits[0] = abc::Abc_Var2Lit( SelectVar( i, 1,3,5), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 ); 
			  
			  pLits[0] = abc::Abc_Var2Lit( OperVar( 0,i ), 0 );
			   abc::sat_solver_addclause(Sat, pLits, pLits + 1 );
		}
		else if (i == 4)
		{
			
			  pLits[0] = abc::Abc_Var2Lit( SelectVar( i, 1,3,5), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 ); 
			  
			  pLits[0] = abc::Abc_Var2Lit( OperVar( 2,i ), 0 );
			   abc::sat_solver_addclause(Sat, pLits, pLits + 1 );
		}
		else if (i == 5)
		{
			
			  pLits[0] = abc::Abc_Var2Lit( SelectVar( i, 1,3,5), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 ); 
			  
			  pLits[0] = abc::Abc_Var2Lit( OperVar( 3,i ), 0 );
			   abc::sat_solver_addclause(Sat, pLits, pLits + 1 );
		}
		else if (i == 6)
		{
			
			  pLits[0] = abc::Abc_Var2Lit( SelectVar( i, 8,9,10), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 ); 
			  
			  pLits[0] = abc::Abc_Var2Lit( OperVar( 1,i ), 0 );
			   abc::sat_solver_addclause(Sat, pLits, pLits + 1 );
		}
		else if (i == 7)
		{
			
			  pLits[0] = abc::Abc_Var2Lit( SelectVar( i, 1,3,10), 0 );
			  abc::sat_solver_addclause(Sat, pLits, pLits + 1 ); 
			  
			  pLits[0] = abc::Abc_Var2Lit( OperVar( 3,i ), 0 );
			   abc::sat_solver_addclause(Sat, pLits, pLits + 1 );
		}
	}
	
	return 1; 
}

int create_tt_clauses( int t )
{
	
    int i, j, k, h, w;
    int pLits[2];

    for ( i = 0; i < nGates; ++i )
    {
        /* main clauses */
        for ( j = 0; j < SpecVars + i; ++j )
            for ( k = j + 1; k < SpecVars + i; ++k )
				for ( w = k + 1; w < SpecVars + i; ++w)
            {
				////std::cout << j << k << w << std::endl; 
                create_main_clauses(  t, i, j, k, w,  0, 0, 0, 1 );
				create_main_clauses(  t, i, j, k, w,  0, 0, 1, 0 );
				create_main_clauses(  t, i, j, k, w,  0, 0, 1, 1 );
				create_main_clauses(  t, i, j, k, w,  0, 1, 0, 0 );
				create_main_clauses(  t, i, j, k, w,  0, 1, 0, 1 );
				create_main_clauses(  t, i, j, k, w,  0, 1, 1, 0 );
				create_main_clauses(  t, i, j, k, w,  0, 1, 1, 1 );
                create_main_clauses(  t, i, j, k, w,  1, 0, 0, 1 );
				create_main_clauses(  t, i, j, k, w,  1, 0, 0, 0 ); 
				create_main_clauses(  t, i, j, k, w,  1, 0, 1, 0 );
				create_main_clauses(  t, i, j, k, w,  1, 0, 1, 1 );
				create_main_clauses(  t, i, j, k, w,  1, 1, 0, 0 );
				create_main_clauses(  t, i, j, k, w,  1, 1, 0, 1 );
				create_main_clauses(  t, i, j, k, w,  1, 1, 1, 0 );
				create_main_clauses(  t, i, j, k, w,  1, 1, 1, 1 );
            }

            for ( h = 0; h < SpecFunc; ++h )
            {
                pLits[0] = abc::Abc_Var2Lit( OutputVar(  h, i ), 1 ); //complemented !ghi
                pLits[1] = abc::Abc_Var2Lit( SimVar( i, t ), 1 - tt_Spec[h][t + 1] ); // xit complemented ornot according to value  1 - tt_Spec[h << 2][t + 1] (make for each  t)
				
                if ( !abc::sat_solver_addclause( Sat, pLits, pLits + 2 ) )
                    return 0;
            }
    }
    return 1;
}

std::vector<unsigned> equal(std::vector<unsigned> c, std::map<unsigned, std::vector<unsigned>> LUT_num_comb)
{
	assert (c.size() == 3); 
	std::vector<unsigned> solution; 
	auto compare_one = LUT_num_comb[c[0]]; 
	auto compare_two = LUT_num_comb[c[1]]; 
	auto compare_third = LUT_num_comb[c[2]]; 
	
	std::vector<unsigned> equal_one; 
	
	for ( auto & g : compare_one)
	{
		if ( g > SpecVars)
		{
			for ( auto & h : compare_two)
			{
				if ( g == h)
				{
					equal_one.push_back(g); 
				}
			}
		}
	}
	
	for (auto& g : compare_third)
	{
		for ( auto & e : equal_one)
		{
			if ( g == e)
				solution.push_back(g); 
		}
	}
	
	return solution; 
}

int FO_clause_limited (std::vector<std::pair<mign_node, std::vector<int>>> node_fo)   // FO_clause is too slow. Then I will apply the constraints only to nodes that have FO > 3. First time I do the computation I will not add any of this constraints..I will add them only later, if is the case 
{
	int pLits[4];
	int a, i, ii, iii, j , k , w, jj, kk , ww, jjj, kkk, www; 
	std::cout << " FO clause limited " << std::endl; 
	for ( a = 3; a < nGates; ++a)
	{
		for ( auto& n : node_fo)
		{
			if ( a + SpecVars + 1 == n.first)
			{
				assert (n.second.size() > 3); 
				i = n.second[0]; 
				ii = n.second[1]; 
				iii = n.second[2]; 
				
				std::vector<std::vector<unsigned>> d; 
				std::map<unsigned, std::vector<unsigned>> LUT_num_comb; 
				unsigned number; 
				std::vector<unsigned> djkw; 
		        for ( j = a; j < SpecVars + i; ++j )
		            for ( k = j + 1; k < SpecVars + i; ++k )
						for ( w = k + 1; w < SpecVars + i; ++w)
				{
					
					number = 0;
					for (auto x = 0; x < j; x++)
					{
						number = number + ((SpecVars  + i -1 - x) * (SpecVars + i - 2 - x))/2;
					}
					number = number + ( -(k-j-1) * (  k -j- 2 * ( SpecVars - 1 + i -j ) ) ) / 2 + ( w - k - 1 ) ;
					std::vector<unsigned> small; 
					small.push_back(j); 
					small.push_back(k);
					small.push_back(w);
					auto it = LUT_num_comb.find(number);
					if (it == LUT_num_comb.end())
						LUT_num_comb.insert({number,small}); 
					djkw.push_back(number); 
				    
				}
		        for ( j = 0; j < k; ++j )
		            for ( k = a; k < SpecVars + i; ++k )
						for ( w = k + 1; w < SpecVars + i; ++w)
				{
					
					number = 0;
					for (auto x = 0; x < j; x++)
					{
						number = number + ((SpecVars  + i -1 - x) * (SpecVars + i - 2 - x))/2;
					}
					number = number + ( -(k-j-1) * (  k -j- 2 * ( SpecVars - 1 + i -j ) ) ) / 2 + ( w - k - 1 ) ;
					std::vector<unsigned> small; 
					small.push_back(j); 
					small.push_back(k);
					small.push_back(w);
					auto it = LUT_num_comb.find(number);
					if (it == LUT_num_comb.end())
						LUT_num_comb.insert({number,small}); 
					djkw.push_back(number); 
				    
				}
		        for ( j = 0; j < SpecVars + i; ++j )
		            for ( k = j + 1; k < w; ++k )
						for ( w = a; w < SpecVars + i; ++w)
				{
					
					number = 0;
					for (auto x = 0; x < j; x++)
					{
						number = number + ((SpecVars  + i -1 - x) * (SpecVars + i - 2 - x))/2;
					}
					number = number + ( -(k-j-1) * (  k -j- 2 * ( SpecVars - 1 + i -j ) ) ) / 2 + ( w - k - 1 ) ;
					std::vector<unsigned> small; 
					small.push_back(j); 
					small.push_back(k);
					small.push_back(w);
					auto it = LUT_num_comb.find(number);
					if (it == LUT_num_comb.end())
						LUT_num_comb.insert({number,small}); 
					djkw.push_back(number); 
				    
				}
				
				d.push_back(djkw); 
	
				std::vector<unsigned> djjkkww; 
		        for ( jj = a; jj < SpecVars + ii; ++jj )
		            for ( kk = jj + 1; kk < SpecVars + ii; ++kk )
						for ( ww = kk + 1; ww < SpecVars + ii; ++ww)
				{
					//if ((jj > SpecVars) || ( kk > SpecVars) || ( ww > SpecVars))
					//{
						number = 0;  
					for (auto x = 0; x < jj; x++)
					{
						number = number + ((SpecVars  + ii -1 - x) * (SpecVars + ii - 2 - x))/2;
					}
					number = number + ( -(kk-jj-1) * (  kk -jj- 2 * ( SpecVars - 1 + ii -jj ) ) ) / 2 + ( ww - kk - 1 ) ;
					std::vector<unsigned> small; 
					small.push_back(j); 
					small.push_back(k);
					small.push_back(w);
					auto it = LUT_num_comb.find(number);
					if (it == LUT_num_comb.end())
						LUT_num_comb.insert({number,small}); 
					djjkkww.push_back(number); 
				   // }
				}
		        for ( jj = 0; jj < k; ++jj )
		            for ( kk = a; kk < SpecVars + ii; ++kk )
						for ( ww = kk + 1; ww < SpecVars + ii; ++ww)
				{
					//if ((jj > SpecVars) || ( kk > SpecVars) || ( ww > SpecVars))
					//{
						number = 0;  
					for (auto x = 0; x < jj; x++)
					{
						number = number + ((SpecVars  + ii -1 - x) * (SpecVars + ii - 2 - x))/2;
					}
					number = number + ( -(kk-jj-1) * (  kk -jj- 2 * ( SpecVars - 1 + ii -jj ) ) ) / 2 + ( ww - kk - 1 ) ;
					std::vector<unsigned> small; 
					small.push_back(j); 
					small.push_back(k);
					small.push_back(w);
					auto it = LUT_num_comb.find(number);
					if (it == LUT_num_comb.end())
						LUT_num_comb.insert({number,small}); 
					djjkkww.push_back(number); 
				   // }
				}
		        for ( jj = 0; jj < SpecVars + i; ++jj )
		            for ( kk = jj + 1; kk < ww; ++kk )
						for ( ww = a; ww < SpecVars + ii; ++ww)
				{
					//if ((jj > SpecVars) || ( kk > SpecVars) || ( ww > SpecVars))
					//{
						number = 0;  
					for (auto x = 0; x < jj; x++)
					{
						number = number + ((SpecVars  + ii -1 - x) * (SpecVars + ii - 2 - x))/2;
					}
					number = number + ( -(kk-jj-1) * (  kk -jj- 2 * ( SpecVars - 1 + ii -jj ) ) ) / 2 + ( ww - kk - 1 ) ;
					std::vector<unsigned> small; 
					small.push_back(j); 
					small.push_back(k);
					small.push_back(w);
					auto it = LUT_num_comb.find(number);
					if (it == LUT_num_comb.end())
						LUT_num_comb.insert({number,small}); 
					djjkkww.push_back(number); 
				   // }
				}
				d.push_back(djjkkww); 
		
				std::vector<unsigned> djjjkkkwww; 
		        for ( jjj = a; jjj < SpecVars + iii; ++jjj )
		            for ( kkk = jjj + 1; kkk < SpecVars + iii; ++kkk )
						for ( www = kkk + 1; www < SpecVars + iii; ++www)
				{
					//if ((jjj > SpecVars) || ( kkk > SpecVars) || ( www > SpecVars))
					//{
						number = 0; 
					for (auto x = 0; x < jjj; x++)
					{
						number = number + ((SpecVars  + iii -1 - x) * (SpecVars + iii - 2 - x))/2;
					}
					number = number + ( -(kkk-jjj-1) * (  kkk -jjj- 2 * ( SpecVars - 1 + iii -jjj ) ) ) / 2 + ( www - kkk - 1 ) ;
					std::vector<unsigned> small; 
					small.push_back(j); 
					small.push_back(k);
					small.push_back(w);
					auto it = LUT_num_comb.find(number);
					if (it == LUT_num_comb.end())
						LUT_num_comb.insert({number,small}); 
					djjjkkkwww.push_back(number); 
				    //}
				}
		        for ( jjj = 0; jjj < kkk; ++jjj )
		            for ( kkk = a; kkk < SpecVars + iii; ++kkk )
						for ( www = kkk + 1; www < SpecVars + iii; ++www)
				{
					//if ((jjj > SpecVars) || ( kkk > SpecVars) || ( www > SpecVars))
					//{
						number = 0; 
					for (auto x = 0; x < jjj; x++)
					{
						number = number + ((SpecVars  + iii -1 - x) * (SpecVars + iii - 2 - x))/2;
					}
					number = number + ( -(kkk-jjj-1) * (  kkk -jjj- 2 * ( SpecVars - 1 + iii -jjj ) ) ) / 2 + ( www - kkk - 1 ) ;
					std::vector<unsigned> small; 
					small.push_back(j); 
					small.push_back(k);
					small.push_back(w);
					auto it = LUT_num_comb.find(number);
					if (it == LUT_num_comb.end())
						LUT_num_comb.insert({number,small}); 
					djjjkkkwww.push_back(number); 
				    //}
				}
		        for ( jjj = 0; jjj < SpecVars + iii; ++jjj )
		            for ( kkk = jjj + 1; kkk < www; ++kkk )
						for ( www = a; www < SpecVars + iii; ++www)
				{
					//if ((jjj > SpecVars) || ( kkk > SpecVars) || ( www > SpecVars))
					//{
						number = 0; 
					for (auto x = 0; x < jjj; x++)
					{
						number = number + ((SpecVars  + iii -1 - x) * (SpecVars + iii - 2 - x))/2;
					}
					number = number + ( -(kkk-jjj-1) * (  kkk -jjj- 2 * ( SpecVars - 1 + iii -jjj ) ) ) / 2 + ( www - kkk - 1 ) ;
					std::vector<unsigned> small; 
					small.push_back(j); 
					small.push_back(k);
					small.push_back(w);
					auto it = LUT_num_comb.find(number);
					if (it == LUT_num_comb.end())
						LUT_num_comb.insert({number,small}); 
					djjjkkkwww.push_back(number); 
				    //}
				}
				d.push_back(djjjkkkwww); 
				assert (d.size() == 3); 
		
				/* All combinations */
			    std::vector<unsigned> a(4,0u); 
			    std::vector<unsigned> m(4,2u); 
	
				std::vector<std::vector<unsigned>> combinations; 
		       
				for ( auto y = 1; y < m.size(); y++)
				{
					auto h = d[y-1].size() - 1; 
					m[y] = d[y-1][h]; 
				}
			    mixed_radix( a, m, [&]( const std::vector<unsigned>& a ) 
				    {
					auto c = a; 
					c.erase (c.begin() + 0); 
					combinations.push_back(c); 
			
					return false; 
				    }); 
	
					 
			for (auto& c : combinations)
			{
				const auto func = equal(c, LUT_num_comb); 
				if (func.size() > 0) 
				{
				   pLits[0] = abc::Abc_Var2Lit( SelectVar( i, LUT_num_comb.at(c[0])[0], LUT_num_comb.at(c[0])[1], LUT_num_comb.at(c[0])[2] ), 1 );
				   pLits[1] = abc::Abc_Var2Lit( SelectVar( ii, LUT_num_comb.at(c[1])[0], LUT_num_comb.at(c[1])[1], LUT_num_comb.at(c[1])[2] ), 1 );
				   pLits[2] = abc::Abc_Var2Lit( SelectVar( iii, LUT_num_comb.at(c[2])[0], LUT_num_comb.at(c[2])[1], LUT_num_comb.at(c[2])[2] ), 1 );
		   
					   for (auto gate = iii + 1; gate < nGates; gate++)
					   {
						   if (func.size() == 1)
						   {
					    
							   auto hj = func[0];
							   for ( auto hk = hj + 1; hk < SpecVars + gate; hk++)
									for ( auto hw = hk + 1; hw < SpecVars + gate; hw++)
							   {
							   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
								 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
							   }
					  
							   auto hk = func[0];
							   for (auto hj = 0; hj < hk; hj++ )
									for ( auto hw = hk + 1; hw < SpecVars + gate; hw++)
							   {
							   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
								 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
							   }
					   
							  auto hw = func[0];
							   for (auto hj = 0; hj < SpecVars + gate; hj++ )
								   for ( auto hk = hj + 1; hk < hw; hk++)
							   {
							   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
								 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
							   }
						   }
						   if (func.size() == 2)
						   {
					   
							   auto hj = func[0];
							   auto hk = func[1];
							   for ( auto hw = hk + 1; hw < SpecVars + gate; hw++)
							   {
							   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
								 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
							   }
					   
							   hk = func[0];
							   auto hw = func[1];
							   for (auto hj = 0; hj < hk; hj++ )
							   {
							   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
								 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
							   }
					
							   hj = func[0];
							   hw = func[1];
							   for ( auto hk = hj + 1; hk < hw; hk++)
							   {
							   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
								 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
							   }
						   }
						   if (func.size() == 3)
						   {
					  
							   auto hj = func[0];
							   auto hk = func[1];
							   auto hw = func[2];
							   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
								 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
						   }
					   }
				    }
			    }
			}
		}
	}
	return 1; 
}

/* limiting fan-out using a sort network. Sort variables sijkw and save them into variables o. Then when 000001111 say that we want the forth = 0 if fanout = 3. */
/*int FO_clause_sortnet ()  
{
	unsigned i, j, k , w, o; 
	std::vector<int> iLits, oLits; 
	o=0;
	for ( i = 0; i < nGates; ++i )  
		{
	        for ( j = 0; j < SpecVars + i; ++j )
	            for ( k = j + 1; k < SpecVars + i; ++k )
					for ( w = k + 1; w < SpecVars + i; ++w)
			{
				// secondo me qui devo 1. aggiungere select vars in un vettore iLits.push_back(abc::Abc_Var2Lit( SelectVars( i,j,k,w), 1 ));
				// 2. aggiungere oLits.push_back(abc::Abc_Var2Lit( Ordered_SelectVar( i, o ), 1 ));
				o++; 
			}
			//qui aggiungere sat_pairwise_cardinality_network( S& solver, iLits, int sid, oLits ); 
			// dovrebbe fare tutto da solo ;) 
		} 
}
*/
int FO_clause ()
{
	
    unsigned i, ii, iii, j, k, w, jj, kk, ww, jjj, kkk, www; 
    int pLits[4];

    for ( i = 1; i < nGates; ++i )   //for gates ;) 
        for ( ii = i + 1; ii < nGates; ++ii )
			for ( iii = ii + 1; iii < nGates; ++iii )
	{
		std::vector<std::vector<unsigned>> d; 
		std::map<unsigned, std::vector<unsigned>> LUT_num_comb; 
		unsigned number; 
		std::vector<unsigned> djkw; 
        for ( j = 0; j < SpecVars + i; ++j )
            for ( k = j + 1; k < SpecVars + i; ++k )
				for ( w = k + 1; w < SpecVars + i; ++w)
		{
			//if ((j > SpecVars) || ( k > SpecVars) || ( w > SpecVars))
			//{
				number = 0;
			for (auto x = 0; x < j; x++)
			{
				number = number + ((SpecVars  + i -1 - x) * (SpecVars + i - 2 - x))/2;
			}
			number = number + ( -(k-j-1) * (  k -j- 2 * ( SpecVars - 1 + i -j ) ) ) / 2 + ( w - k - 1 ) ;
			std::vector<unsigned> small; 
			small.push_back(j); 
			small.push_back(k);
			small.push_back(w);
			auto it = LUT_num_comb.find(number);
			if (it == LUT_num_comb.end())
				LUT_num_comb.insert({number,small}); 
			djkw.push_back(number); 
		    //}
		}
		d.push_back(djkw); 
	
		std::vector<unsigned> djjkkww; 
        for ( jj = 0; jj < SpecVars + ii; ++jj )
            for ( kk = jj + 1; kk < SpecVars + ii; ++kk )
				for ( ww = kk + 1; ww < SpecVars + ii; ++ww)
		{
			//if ((jj > SpecVars) || ( kk > SpecVars) || ( ww > SpecVars))
			//{
				number = 0;  
			for (auto x = 0; x < jj; x++)
			{
				number = number + ((SpecVars  + ii -1 - x) * (SpecVars + ii - 2 - x))/2;
			}
			number = number + ( -(kk-jj-1) * (  kk -jj- 2 * ( SpecVars - 1 + ii -jj ) ) ) / 2 + ( ww - kk - 1 ) ;
			std::vector<unsigned> small; 
			small.push_back(j); 
			small.push_back(k);
			small.push_back(w);
			auto it = LUT_num_comb.find(number);
			if (it == LUT_num_comb.end())
				LUT_num_comb.insert({number,small}); 
			djjkkww.push_back(number); 
		   // }
		}
		d.push_back(djjkkww); 
		
		std::vector<unsigned> djjjkkkwww; 
        for ( jjj = 0; jjj < SpecVars + iii; ++jjj )
            for ( kkk = jjj + 1; kkk < SpecVars + iii; ++kkk )
				for ( www = kkk + 1; www < SpecVars + iii; ++www)
		{
			//if ((jjj > SpecVars) || ( kkk > SpecVars) || ( www > SpecVars))
			//{
				number = 0; 
			for (auto x = 0; x < jjj; x++)
			{
				number = number + ((SpecVars  + iii -1 - x) * (SpecVars + iii - 2 - x))/2;
			}
			number = number + ( -(kkk-jjj-1) * (  kkk -jjj- 2 * ( SpecVars - 1 + iii -jjj ) ) ) / 2 + ( www - kkk - 1 ) ;
			std::vector<unsigned> small; 
			small.push_back(j); 
			small.push_back(k);
			small.push_back(w);
			auto it = LUT_num_comb.find(number);
			if (it == LUT_num_comb.end())
				LUT_num_comb.insert({number,small}); 
			djjjkkkwww.push_back(number); 
		    //}
		}
		d.push_back(djjjkkkwww); 
		assert (d.size() == 3); 
		
		/* All combinations */
	    std::vector<unsigned> a(4,0u); 
	    std::vector<unsigned> m(4,2u); 
	
		std::vector<std::vector<unsigned>> combinations; 
       // std::vector<unsigned> func; 
		for ( auto y = 1; y < m.size(); y++)
		{
			auto h = d[y-1].size() - 1; 
			m[y] = d[y-1][h]; 
		}
	    mixed_radix( a, m, [&]( const std::vector<unsigned>& a ) 
		    {
			auto c = a; 
			c.erase (c.begin() + 0); 
			combinations.push_back(c); 
			
			return false; 
		    }); 
	
			//std::cout << " comb " << std::endl; 
	for (auto& c : combinations)
	{
		const auto func = equal(c, LUT_num_comb); 
		if (func.size() > 0) 
		{
		   pLits[0] = abc::Abc_Var2Lit( SelectVar( i, LUT_num_comb.at(c[0])[0], LUT_num_comb.at(c[0])[1], LUT_num_comb.at(c[0])[2] ), 1 );
		   pLits[1] = abc::Abc_Var2Lit( SelectVar( ii, LUT_num_comb.at(c[1])[0], LUT_num_comb.at(c[1])[1], LUT_num_comb.at(c[1])[2] ), 1 );
		   pLits[2] = abc::Abc_Var2Lit( SelectVar( iii, LUT_num_comb.at(c[2])[0], LUT_num_comb.at(c[2])[1], LUT_num_comb.at(c[2])[2] ), 1 );
		   
			   for (auto gate = iii + 1; gate < nGates; gate++)
			   {
				   if (func.size() == 1)
				   {
					    
					   auto hj = func[0];
					   for ( auto hk = hj + 1; hk < SpecVars + gate; hk++)
							for ( auto hw = hk + 1; hw < SpecVars + gate; hw++)
					   {
					   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
						 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
					   }
					  
					   auto hk = func[0];
					   for (auto hj = 0; hj < hk; hj++ )
							for ( auto hw = hk + 1; hw < SpecVars + gate; hw++)
					   {
					   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
						 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
					   }
					   
					  auto hw = func[0];
					   for (auto hj = 0; hj < SpecVars + gate; hj++ )
						   for ( auto hk = hj + 1; hk < hw; hk++)
					   {
					   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
						 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
					   }
				   }
				   if (func.size() == 2)
				   {
					   
					   auto hj = func[0];
					   auto hk = func[1];
					   for ( auto hw = hk + 1; hw < SpecVars + gate; hw++)
					   {
					   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
						 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
					   }
					   
					   hk = func[0];
					   auto hw = func[1];
					   for (auto hj = 0; hj < hk; hj++ )
					   {
					   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
						 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
					   }
					
					   hj = func[0];
					   hw = func[1];
					   for ( auto hk = hj + 1; hk < hw; hk++)
					   {
					   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
						 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
					   }
				   }
				   if (func.size() == 3)
				   {
					  
					   auto hj = func[0];
					   auto hk = func[1];
					   auto hw = func[2];
					   	 pLits[3] = abc::Abc_Var2Lit( SelectVar( gate, hj, hk, hw ), 1 );
						 abc::sat_solver_addclause( Sat, pLits, pLits + 3 ); 
				   }
			   }
		    }
	    }
    }
    return 1;
}

int create_clauses(std::vector<std::pair<mign_node, std::vector<int>>> node_fo)
{
    int h, i, j, k, w, t, ii, jj, kk, ww, p, q, u;
    int pLits[2];
    int uLits[nGates]; 
	
    for ( t = 0; t < Rows; ++t )
    {
            if ( !create_tt_clauses( t ) ) 
                return 0;
    }
   
	//tt 1101001100100100
    /* if there is only one output, we know it must point to the last gate  */
    if ( SpecFunc == 1 )
    {
        for ( i = 0; i < nGates - 1; ++i )
        {
            pLits[0] = abc::Abc_Var2Lit( OutputVar( 0, i ), 1 );
            if ( !abc::sat_solver_addclause( Sat, pLits, pLits + 1 ) )
                return 0;
        }
        pLits[0] = abc::Abc_Var2Lit( OutputVar( 0, nGates - 1 ), 0 );
        if ( !abc::sat_solver_addclause( Sat, pLits, pLits + 1 ) )
            return 0;
    }
    else
    {
        /* some output is selected */
        for ( h = 0; h < SpecFunc; ++h )
        {
            for ( i = 0; i < nGates; ++i )
				uLits[i] = abc::Abc_Var2Lit( OutputVar( h, i ), 0 ); 	
			 abc::sat_solver_addclause( Sat, uLits, uLits + nGates );
        }
    }

    /* each gate has three operands */
    for ( i = 0; i < nGates; ++i )
    {
		int vLits[( ( SpecVars + i ) * ( SpecVars + i - 1 ) * ( SpecVars + i - 2)) / 6];
		////std::cout << ( ( SpecVars + i ) * ( SpecVars + i - 1 ) * ( SpecVars + i - 2)) / 6 << std::endl; 
        jj = 0;
        for ( j = 0; j < SpecVars + i; ++j )
            for ( k = j + 1; k < SpecVars + i; ++k )
				for ( w = k + 1; w < SpecVars + i; ++w)
			{
				vLits[jj++] = abc::Abc_Var2Lit( SelectVar(  i, j, k , w), 0 );  
				////std::cout << " j k w " << j << k << w << std::endl;
				} 
        abc::sat_solver_addclause( Sat, vLits, vLits + jj );
    }
	
	
	if (MaxDepth > 0)
		Depthclause();   // FOR DEPTH 

    //ADD_FIXED_CLAUSES(); // debug 

     for ( i = 0; i < nGates; ++i )
        {
			//int pLits[2]; 
			
			// first maj operation <xyz> = M3
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
				////std::cout << " gate var i 0 0 1 , 0" << std::endl; 
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
				////std::cout << " gate var i 0 1 0 , 0" << std::endl; 
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
				////std::cout << " gate var i 0 1 1 , 1" << std::endl; 
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
				////std::cout << " gate var i 1 0 0  , 0" << std::endl; 
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
				////std::cout << " gate var i 1 0 1  , 1" << std::endl; 
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
				////std::cout << " gate var i 1 1 0  , 1" << std::endl; 
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
				////std::cout << " gate var i 1 1 1  , 1" << std::endl; 
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
			// second maj operation <!xyz> = M3
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
			// second maj operation <x!yz> = M3
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
			// second maj operation <xy!z> = M4
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <0bc> = AND1
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <1bc> = AND1 neg 1
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				
				// second maj operation <0!bc> = AND1 neg 2
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				
				// second maj operation <0b!c> = AND1 neg 3
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <a0c> = AND2
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				
				// second maj operation <!a0c> = AND2 neg 1
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <a1c> = AND2 neg 2
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <a0!c> = AND2 neg 3
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <ab0> = AND3
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <!ab0> = AND3 neg 1
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <a!b0> = AND3 neg 2
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <ab1> = AND3 neg 3
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				//FINAL OR 
				int iLits[16]; 
				for ( auto f = 0; f < Noper; f++)
				{
					iLits[f] = abc::Abc_Var2Lit( OperVar(f,i), 0 );
				}
				
				abc::sat_solver_addclause( Sat, iLits, iLits + 16 ) ;
					
        }	
		
		 
		/*if (MaxFanout > 0)
		{
			int start_s=clock();
			FO_clause (); 
			int stop_s=clock();
			std::cout << "FO execution time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC)*1000 << std::endl;
		}*/
		
		if (node_fo.size() != 0)
		{
			int start_s=clock();
			FO_clause_limited(node_fo); 
			int stop_s=clock();
			std::cout << "FO limited execution time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC)*1000 << std::endl;
		}
		 
		/*if (MaxFanout > 0)
		{
			int start_s=clock();
			FO_clause_sortnet (); 
			int stop_s=clock();
			std::cout << "FO execution time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC) << std::endl;
		}*/
		
	    /* EXTRA clauses: use gate i at least once */
		std::vector<int> vLits; 

	    for ( i = 0; i < nGates; ++i )
	    {
	        jj = 0;
	        for ( h = 0; h < SpecFunc; ++h )
	            vLits.push_back(abc::Abc_Var2Lit( OutputVar(  h, i ), 0 )) ;
	        for ( ii = i + 1; ii < nGates; ++ii )
	        {
	            for ( j = 0; j < SpecVars + i; ++j )
					for (k = j + 1; k < SpecVars + i; k++)
				{
					vLits.push_back(abc::Abc_Var2Lit( SelectVar( ii, j, k, SpecVars + i), 0 )) ;
				}
	                      
	            for ( k = SpecVars + i + 1; k < SpecVars + ii; k++ )
					 for ( w = k + 1; w < SpecVars + ii; w++ )
				{
					  vLits.push_back(abc::Abc_Var2Lit( SelectVar( ii, SpecVars + i, k , w ), 0 )) ;
				}
	                   
	            for ( j = 0; j < SpecVars + i; j++ )
					for (w = SpecVars + i + 1; w < SpecVars + ii; w++)
				{
					vLits.push_back(abc::Abc_Var2Lit( SelectVar( ii, j, SpecVars + i, w ), 0 )) ;  
				}
	                     
	        }
			int array[vLits.size()]; 
			std::copy(vLits.begin(), vLits.end(), array);
            abc::sat_solver_addclause( Sat, array , array + vLits.size());
	    }

	    /* EXTRA clauses: co-lexicographic order */
	    for ( i = 0; i < nGates - 1; ++i )
	    {
			for ( w = 3; w < SpecVars + i; w++)
			{
				for ( k = 2; k < w; k++)
				{
					for (j = 1; j < k; j++)
						for ( jj = 0; jj < j; ++jj)
					{
						
	                    pLits[0] = abc::Abc_Var2Lit( SelectVar( i, j, k, w ), 1 );
	                    pLits[1] = abc::Abc_Var2Lit( SelectVar( i + 1, jj, k , w), 1 );
						abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
					}
				}
				
				
				for ( k = 1; k < w; k++)
				{
		            for ( j = 0; j < k; ++j )
		                for ( kk = 1; kk < k; ++kk )
		                    for ( jj = 0; jj < kk; ++jj )
		                    {
								//std::cout << " caso 2" << std::endl;
		                        pLits[0] = abc::Abc_Var2Lit( SelectVar( i, j, k, w ), 1 );
		                        pLits[1] = abc::Abc_Var2Lit( SelectVar( i + 1, jj, kk , w), 1 );
								abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
		                    }
				}
				
				for ( k = 1; k < w; k++)
				{
		            for ( j = 0; j < k; ++j )
						for ( ww = 1; ww < w; ++ww)
		                    for ( kk = 1; kk < ww; ++kk )
		                         for ( jj = 0; jj < kk; ++jj )
		                         {
		                             pLits[0] = abc::Abc_Var2Lit( SelectVar(  i, j, k, w ), 1 );
		                             pLits[1] = abc::Abc_Var2Lit( SelectVar( i + 1, jj, kk , ww), 1 );
									 abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
		                         }
				}
				
			}
	           
	    }
	    
	    /* EXTRA clauses: symmetric variables */
	    if ( SpecFunc == 1 ) 
	    {
			auto pairs = tt_symmetric (tt_Spec[0]); 
			std::vector<int> hLits; 
		    for ( auto& pa : pairs)
		    {
		         auto p = pa.first; 
		         auto q = pa.second; 
		
	             if ( eVerbose )
	             printf( "variables %d and %d are symmetric\n", p, q );
	             for ( i = 0; i < nGates; ++i )
					 for ( k = 1; k < q; ++k)
	                     for ( j = 0; j < k; ++j )
	                     {
	                        if (( j == p ) || (k == p)) continue;
							hLits.push_back(abc::Abc_Var2Lit( SelectVar( i, j, k, q ), 1 ) );
	                        for ( ii = 0; ii < i; ++ii )
								for ( ww = 2; ww < SpecVars + ii; ++ww)
	                                 for ( kk = 1; kk < ww; ++kk )
	                                    for ( jj = 0; jj < kk; ++jj )
	                                        if ( jj == p || kk == p || ww == p )
							{
								hLits.push_back(abc::Abc_Var2Lit( SelectVar( ii, jj, kk, ww ), 0 ) );
							}
							int array[hLits.size()]; 
							std::copy(hLits.begin(), hLits.end(), array);
	                        abc::sat_solver_addclause( Sat, array , array + hLits.size());

	                        }
	                }
				}
    return 1;
}

int Sat_Solve()
{
    int status;
    abc::abctime timeStart, timeDelta;

    timeStart = abc::Abc_Clock();
    status = sat_solver_solve( Sat, NULL, NULL, nBTLimit, 0, 0, 0 );
    timeDelta = abc::Abc_Clock() - timeStart;

	timeSat += timeDelta;

    if ( status == abc::l_True )
    {
        nSatCalls++;
        timeSatSat += timeDelta;
        return 1;
    }
    else if ( status == abc::l_False )
    {
        nUnsatCalls++;
        timeSatUnsat += timeDelta;
        return 0;
    }
    else
    {
        nUndefCalls++;
        timeSatUndef += timeDelta;
        if ( eVerbose )
        {
            printf( "resource limit reached\n" );
        }
        return 2;
    }
}  

void print_debug()
{
	int i, h, j, k , w, nOp, g; 
	
	 for ( i = 0; i < nGates; ++i )
	 {
		 std::cout << " GATE " << i + SpecVars << std::endl; 
		 
 		for (auto t = 0; t < Rows; t++)
			std::cout << SimVar(i,t) << "  " << "x(" << i << "," << t <<  ")" << " = " << abc::sat_solver_var_value(Sat, SimVar(i,t) ) << std::endl;
		
		for ( h = 0; h < SpecFunc; h++)
			std::cout << OutputVar(h,i) << "  " << "g(" << h << "," << i <<  ")" << " = " << abc::sat_solver_var_value(Sat, OutputVar(h,i) ) << std::endl;
		
		std::cout << GateVar(i, 0, 0, 1) << "  " << "f(" << i << "," << 0 << "," << 0 << "," << 1 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,0,0,1) ) << std::endl;
		std::cout << GateVar(i, 0, 1, 0) << "  " << "f(" << i << "," << 0 << "," << 1 << "," << 0 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,0,1,0) ) << std::endl;
		std::cout << GateVar(i, 0, 1, 1) << "  " << "f(" << i << "," << 0 << "," << 1 << "," << 1 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,0,1,1) ) << std::endl;
		std::cout << GateVar(i, 1, 0, 0) << "  " << "f(" << i << "," << 1 << "," << 0 << "," << 0 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,1,0,0) ) << std::endl;
		std::cout << GateVar(i, 1, 0, 1) << "  " << "f(" << i << "," << 1 << "," << 0 << "," << 1 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,1,0,1) ) << std::endl;
		std::cout << GateVar(i, 1, 1, 0) << "  " << "f(" << i << "," << 1 << "," << 1 << "," << 0 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,1,1,0) ) << std::endl;
		std::cout << GateVar(i, 1, 1, 1) << "  " << "f(" << i << "," << 1 << "," << 1 << "," << 1 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,1,1,1) ) << std::endl;
		
		 
	 	for ( w = 0; w < SpecVars + i; ++w)
	         for ( k = 0; k < w; ++k )
	              for ( j = 0; j < k; ++j )
						 {
							 std::cout << SelectVar(i, j, k, w) << "  " << "s(" << i << "," << j << "," << k << "," << w << ")" << " = " << abc::sat_solver_var_value(Sat, SelectVar(i, j, k, w) ) << std::endl;
							
						 }
		
		
	 for ( auto x = 0; x < 16; x++)
		 {
			 std::cout << OperVar(x,i) << "  " << "op(" << x << "," << i << ")" << " = " << abc::sat_solver_var_value(Sat, OperVar(x,i ) ) << std::endl; 
		 }
		 
		 if (MaxDepth > 0)
		{ 
			for (auto l = 0; l <=i ; l++)
		 {
			 std::cout << DepthVar(i,l) << "  " << "d(" << i << "," << l << ")" << " = " << abc::sat_solver_var_value(Sat, DepthVar(i,l ) ) << std::endl; 
		 } 
	 }
	
	 }
}



std::vector<mign_graph> extract_mig( std::string model_name, std::string output_name, bool normal, bool verbose)
{
	std::vector<mign_graph> mign; 
    int nSol, h, i, j, k, nOp, w;
	
	mign.resize(1); // for now only one possible solution ;) 
	
	mign[0].set_name(model_name);
	mign[0].structural_hashing(1) ;   // disable structural hashing 
	
	std::unordered_map<mign_node, mign_function> node_to_function;
	// INPUTS 
	mign[0].get_constant(false);
	mign[0].get_constant(true);
	
	//std::cout << " SpecVars = " << SpecVars<< std::endl; 
	for ( auto inputs = 0; inputs < SpecVars; ++inputs)
	{
		auto name = boost::str( boost::format( "x_%d" ) % inputs);
		node_to_function.insert ({inputs, mign[0].create_pi(name)}); 
	}

    /* gates */
    for ( i = 0; i < nGates; ++i )
    {
		//std::cout << " GATE " << i << std::endl;
		auto flag = 0; 
		std::vector<bool> compl_input (3); 
		if (abc::sat_solver_var_value(Sat, OperVar(0,i ) ))
		{
			flag = 1; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(1,i ) ))
		{
			flag = 1; 
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(2,i ) ))
		{
			flag = 1; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(3,i ) ))
		{
			flag = 1; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(4,i ) ))  // AND 0bc
		{
			flag = 2; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(7,i ) ))
		{
			flag = 2;
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(8,i ) ))
		{
			flag = 2; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(9,i ) ))
		{
			flag = 2; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(5,i ) ))  // AND a0c
		{
			flag = 3; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(10,i ) ))
		{
			flag = 3;
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(11,i ) ))
		{
			flag = 3; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(12,i ) ))
		{
			flag = 3; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(6,i ) ))  // AND ab0
		{
			flag = 4; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(13,i ) ))
		{
			flag = 4;
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(14,i ) ))
		{
			flag = 4; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(15,i ) ))
		{
			flag = 4; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
       // nOp  = abc::sat_solver_var_value(Sat, GateVar( i, 0, 0, 1 ) );
	
       
		for ( w = 0; w < SpecVars + i; ++w)
            for ( k = 0; k < w; ++k )
                for ( j = 0; j < k; ++j )
                     if ( abc::sat_solver_var_value( Sat, SelectVar( i, j, k, w ) ) )
                     {
						//printf( " and operands %d and %d and %d", j, k, w );
						std::vector<mign_function> operands;
						if (flag == 1)
						{
							
							operands.push_back(node_to_function.at(j)^compl_input[0]); 
							operands.push_back(node_to_function.at(k)^compl_input[1]); 
							operands.push_back(node_to_function.at(w)^compl_input[2]); 
							node_to_function.insert({SpecVars + i, mign[0].create_maj(operands)});
							
						}
						
						else if ( flag == 2)
						{
							
							operands.push_back(node_to_function.at(k)^compl_input[1]); 
							operands.push_back(node_to_function.at(w)^compl_input[2]);
							if (compl_input[0] == 1)
							{
								node_to_function.insert({SpecVars + i, mign[0].create_or(operands)});
							}
							else 
								node_to_function.insert({SpecVars + i, mign[0].create_and(operands)});
							
						}
						else if ( flag == 3)
						{
						
							operands.push_back(node_to_function.at(j)^compl_input[0]); 
							operands.push_back(node_to_function.at(w)^compl_input[2]);
							if (compl_input[1] == 1)
							{
								node_to_function.insert({SpecVars + i, mign[0].create_or(operands)});
							}
							else 
								node_to_function.insert({SpecVars + i, mign[0].create_and(operands)});
						
						}
						else if ( flag == 4)
						{
							
							operands.push_back(node_to_function.at(j)^compl_input[0]); 
							operands.push_back(node_to_function.at(k)^compl_input[1]);
							if (compl_input[2] == 1)
							{
								node_to_function.insert({SpecVars + i, mign[0].create_or(operands)});
							}
							else 
								node_to_function.insert({SpecVars + i, mign[0].create_and(operands)});
							
						}
						 
                        w = SpecVars + i;  // E qui che sto considerando una sola soluzione possibile?? 
						k = w; 
                        break;
                      }
    }


    /* outputs */
	std::cout << SpecFunc << std::endl; 
    for ( h = 0; h < SpecFunc; ++h )
        for ( i = 0; i < nGates; ++i )
            if ( sat_solver_var_value( Sat, OutputVar( h, i ) ) )
            {
                   // printf( "output %d points to gate %d \n", h, SpecVars + i);
					if (!normal)
						mign[0].create_po (create_mign_function(node_to_function.at(SpecVars + i).node, 1), output_name); 
					else 
						mign[0].create_po (create_mign_function(node_to_function.at(SpecVars + i).node, 0), output_name);
            }
			return mign; 
}

std::vector<mign_graph> extract_mig_MO( std::string model_name, std::vector<bool> normal_ori, bool verbose)
{
	std::vector<mign_graph> mign; 
    int nSol, h, i, j, k, nOp, w;
	
	mign.resize(1); // for now only one possible solution ;) 
	
	mign[0].set_name(model_name);
	//mign[0].structural_hashing(1) ;   // disable structural hashing 
	
	std::unordered_map<mign_node, mign_function> node_to_function;
	// INPUTS 
	mign[0].get_constant(false);
	mign[0].get_constant(true);
	
	for ( auto inputs = 0; inputs < SpecVars; ++inputs)
	{
		auto name = boost::str( boost::format( "x_%d" ) % inputs);
		node_to_function.insert ({inputs, mign[0].create_pi(name)}); 
	}

    /* gates */
    for ( i = 0; i < nGates; ++i )
    {
		auto flag = 0; 
		std::vector<bool> compl_input (3); 
		if (abc::sat_solver_var_value(Sat, OperVar(0,i ) ))
		{
			flag = 1; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(1,i ) ))
		{
			flag = 1; 
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(2,i ) ))
		{
			flag = 1; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(3,i ) ))
		{
			flag = 1; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(4,i ) ))  // AND 0bc
		{
			flag = 2; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(7,i ) ))
		{
			flag = 2;
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(8,i ) ))
		{
			flag = 2; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(9,i ) ))
		{
			flag = 2; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(5,i ) ))  // AND a0c
		{
			flag = 3; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(10,i ) ))
		{
			flag = 3;
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(11,i ) ))
		{
			flag = 3; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(12,i ) ))
		{
			flag = 3; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(6,i ) ))  // AND ab0
		{
			flag = 4; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(13,i ) ))
		{
			flag = 4;
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(14,i ) ))
		{
			flag = 4; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(15,i ) ))
		{
			flag = 4; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		} 
	
        nOp  = abc::sat_solver_var_value(Sat, GateVar( i, 0, 0, 1 ) );

       
		for ( w = 0; w < SpecVars + i; ++w)
            for ( k = 0; k < w; ++k )
                for ( j = 0; j < k; ++j )
                     if ( sat_solver_var_value( Sat, SelectVar( i, j, k, w ) ) )
                     {
                       // printf( " and operands %d and %d and %d", j, k, w );
						std::vector<mign_function> operands;
						if (flag == 1)
						{
							operands.push_back(node_to_function.at(j)^compl_input[0]); 
							operands.push_back(node_to_function.at(k)^compl_input[1]); 
							operands.push_back(node_to_function.at(w)^compl_input[2]); 
							node_to_function.insert({SpecVars + i, mign[0].create_maj(operands)});
						}
						
						else if ( flag == 2)
						{
							operands.push_back(node_to_function.at(k)^compl_input[1]); 
							operands.push_back(node_to_function.at(w)^compl_input[2]);
							if (compl_input[0] == 1)
							{
								node_to_function.insert({SpecVars + i, mign[0].create_or(operands)});
							}
							else 
								node_to_function.insert({SpecVars + i, mign[0].create_and(operands)});
						}
						else if ( flag == 3)
						{
							operands.push_back(node_to_function.at(j)^compl_input[0]); 
							operands.push_back(node_to_function.at(w)^compl_input[2]);
							if (compl_input[1] == 1)
							{
								node_to_function.insert({SpecVars + i, mign[0].create_or(operands)});
							}
							else 
								node_to_function.insert({SpecVars + i, mign[0].create_and(operands)});
						}
						else if ( flag == 4)
						{
							operands.push_back(node_to_function.at(j)^compl_input[0]); 
							operands.push_back(node_to_function.at(k)^compl_input[1]);
							if (compl_input[2] == 1)
							{
								node_to_function.insert({SpecVars + i, mign[0].create_or(operands)});
							}
							else 
								node_to_function.insert({SpecVars + i, mign[0].create_and(operands)});
						}
						 
                        w = SpecVars + i;  // E qui che sto considerando una sola soluzione possibile?? 
						k = w; 
                        break;
                      }
    }
		


    /* outputs */
    for ( h = 0; h < SpecFunc; ++h )
        for ( i = 0; i < nGates; ++i )
	   {
		if ( sat_solver_var_value( Sat, OutputVar( h, i ) ) )
            {
                    //printf( "output %d points to gate %d \n", h, SpecVars + i);
					auto output_name = str( format( "f_%d" ) % h ); 
					if (!normal_ori[h])
						mign[0].create_po (create_mign_function(node_to_function.at(SpecVars + i).node, 1), output_name); 
					else 
						mign[0].create_po (create_mign_function(node_to_function.at(SpecVars + i).node, 0), output_name);
					i = nGates; 
				break; 	
            }
		}
			return mign; 
}


		abc::sat_solver * Sat;                  /* SAT solver */
		bool  eVerbose; 
        std::vector<tt> tt_Spec;                          /* specification */
		//std::vector<std::pair<unsigned, unsigned>> symm_pairs; /* symmetric variables in spec */
        unsigned int          SpecVars;             /* number of variables in specification = n */
		int          SpecFunc;             /* number of functions to synthesize = m */
        int          Rows;                 /* number of rows in the specification (without 0) */
        int          MaxDepth;             /* maximum depth (= 3 for plasmonic) */
		int          MaxFanout;            /* maximum fanout (= 3 for plasmonic) */
        //int          nMaxDepthTmp;          /* temporary copy to modify nMaxDepth temporarily */
        //int *        pArrTimeProfile;       /* arrival times of inputs (NULL if arrival times are ignored) */
        //int          pArrTimeProfileTmp[8]; /* temporary copy to modify pArrTimeProfile temporarily */
       // int          nArrTimeDelta;         /* delta to the original arrival times (arrival times are normalized to have 0 as minimum element) */
        //int          nArrTimeMax;           /* maximum normalized arrival time */
        int          nBTLimit = 0;              /* conflict limit */
        //int          fMakeAIG;              /* create AIG instead of general network */
       // word         pTtValues[4];          /* truth table values to assign */

		int          Noper ;                 /* Number of operation allowed */
        int          nGates;                /* number of gates */
        int          nStartGates;           /* number of gates to start search (-1), i.e., to start from 1 gate, one needs to specify 0 */
        int          nMaxGates;             /* maximum number of gates given max. delay and arrival times */
        int          fDecStructure;         /* set to 1 or higher if SpecFunc = 1 and f = x_i OP g(X \ {x_i}), otherwise 0 (determined when solving) */
       // int          pDecVars;              /* mask of variables that can be decomposed at top-level */
      //  word         pTtObjs[100];          /* temporary truth tables */

        int          nSimVars;              /* number of simulation vars x(i, t) */
        int          nOutputVars;           /* number of output variables g(h, i) */
        int          nGateVars;             /* number of gate variables f(i, p, q) */
        int          nSelectVars;           /* number of select variables s(i, j, k) */
        int          nOperVars;             /* number of operations variables op_i */
		int          nDepthVars;            /* number of depth variables d(i,j) */

        int          nOutputOffset;         /* offset where output variables start */
        int          nGateOffset;           /* offset where gate variables start */
        int          nSelectOffset;         /* offset where select variables start */
		int          nOperOffset;            /* offset where possible operations start */
		int          nDepthOffset;          /* offset where depth variables start */
    

        int          fHitResLimit;          /* SAT solver gave up due to resource limit */
		
	    abc::abctime      timeSat;               /* SAT runtime */
	    abc::abctime      timeSatSat;            /* SAT runtime (sat instance) */
	    abc::abctime      timeSatUnsat;          /* SAT runtime (unsat instance) */
	    abc::abctime      timeSatUndef;          /* SAT runtime (undef instance) */
	    abc::abctime      timeInstance;          /* creating instance runtime */
	    abc::abctime      timeTotal;             /* all runtime */


        int          nSatCalls;             /* number of SAT calls */
        int          nUnsatCalls;           /* number of UNSAT calls */
        int          nUndefCalls;           /* number of UNDEF calls */
    };

/******************************************************************************
* Private functions                                                          *
******************************************************************************/

template<typename T>
class exact_mig_abc_manager
{
public:
exact_mig_abc_manager( const spec_representation_mign& spec, const properties::ptr& settings )
       : spec( spec ),
         normal( spec.mign_is_normal() )
{
       /* meta data */
	 model_name          = get( settings, "model_name",          std::string( "exact_new" ) );
	 output_name         = get( settings, "output_name",         std::string( "f" ) );

	 start               = get( settings, "start",               1u );
	 //start_depth         = get(settings,  "start_depth"),         -1); 
  
	 all_solutions       = get( settings, "all_solutions",       false );

       /* encoding */
      
	 timeout             = get( settings, "timeout",             boost::optional<unsigned>() );
     verbose             = get( settings, "verbose",             true );
     very_verbose        = get( settings, "very_verbose",        false );

	 verbose = verbose || very_verbose;
     }
	 
std::vector<T> run()
{
       // check trivial case 
       const auto triv = spec.mign_is_trivial();
       if ( (bool)triv )
           {
           return {create_trivial<T>( triv->first, triv->second )};
           }

       if ( !normal )
          {
          spec.mign_invert(); // we need normal functions 
          }

return exact_mig_abc(); 
}

	 
std::vector<T> exact_mig_abc()
{
  auto k = start;
  auto depth = 3u; 
  auto fanout = -1; 
  std::vector<mign_graph> mign; 
  std::vector<std::pair<mign_node, std::vector<int>>> node_fo; 
  
  while ( true )
  {
	  
     if ( verbose )
     {
		 std::cout << boost::format( "[i] check for realization with %d gates" ) % k << std::endl;
     }
  
     auto inst = create_inst ();
  
     inst->create_var(k, depth, fanout); 
     int start_s=clock();
     inst->create_clauses(node_fo); 
     int stop_s=clock();
	 std::cout << "ALL CLAUSES time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC)*1000 << std::endl;
     start_s=clock();
     const auto result = inst->Sat_Solve(); 
	 stop_s=clock();
	 std::cout << "SAT SOLVE time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC)*1000 << std::endl;
	 
     if ( result == 1)
       {
	   //inst->print_debug();
	   std::vector<std::pair<mign_node, std::vector<int>>> node_fo_p; 
       mign = inst->extract_mig( model_name, output_name, normal, verbose );
	   mign[0] = mign_fo_restricted_opt ( mign[0], 3, 1); 
	   return mign; }
	   
     else if ( result == 2 )
      {
       //last_size = k;
      return std::vector<T>();
      }
    else
      ++k;
  }
}

struct tt_from_spec_visitor : public boost::static_visitor<void>
{
  tt_from_spec_visitor( const std::shared_ptr<exact_inst>& inst ) : inst( inst ) {}

  void operator()( const tt& spec ) const
  {
    inst->tt_from_spec( spec );
  }

  void operator()( const mign_graph& spec ) const
  {
    inst->tt_from_spec( spec );
  }

private:
  const std::shared_ptr<exact_inst>& inst;
};


inline std::shared_ptr<exact_inst> create_inst() const
{
  auto inst = std::make_shared<exact_inst>(spec.mign_num_vars(),verbose,1 ); 
  spec.mign_apply_visitor(tt_from_spec_visitor(inst)); 
  return inst; 
}


template<typename C, typename std::enable_if<std::is_same<mign_graph, C>::value>::type* = nullptr>
mign_graph create_trivial( unsigned id, bool complement )
{
  mign_graph mign;
  
  mign.get_constant(false);
  mign.get_constant(true);

  if ( id == 0u )
  {
	mign.create_po( mign.get_constant(true), output_name );
    //mig_create_po( mig, mig_get_constant( mig, complement ), output_name );
  }
  else
  {
    //const auto& info = mig_info( mig );

    for ( auto i = 0u; i < id; ++i )
    {
		mign.create_pi(str( format( "x_%d" ) % i ));
      //mig_create_pi( mig, str( format( "x%d" ) % i ) );
    }
	mign.create_po( create_mign_function(mign.inputs().back().first,complement), output_name );
    //mig_create_po( mig, {info.inputs.back(), complement}, output_name );
  }
  return mign;
}


private:
  spec_representation_mign spec;
  bool normal;
  unsigned start;
  //int start_depth; 
  //unsigned start_depth;
 // unsigned node_level; 
  //unsigned max_fanout;
  std::string model_name;
  std::string output_name;
  unsigned objective;
  bool incremental;
  bool all_solutions;
  //std::string breaking;
  //bool enc_with_bitvectors;
  boost::optional<unsigned> timeout;
  bool verbose;
  bool very_verbose;
};

class exact_mig_abc_manager_MO
{
public:
exact_mig_abc_manager_MO( const mign_graph& spec, const properties::ptr& settings, const properties::ptr& statistics )
       : spec( spec )
{
       /* meta data */
	 model_name          = get( settings, "model_name",          std::string( "exact_new_MO" ) );
	// output_name         = get( settings, "output_name",         std::string( "f" ) );

	 start               = get( settings, "start",               spec.inputs().size());
	//start_depth         = get(settings,  "start_depth"),          -1); 
  
  
	 all_solutions       = get( settings, "all_solutions",       false );

       /* encoding */
      
	 timeout             = get( settings, "timeout",             boost::optional<unsigned>() );
     verbose             = get( settings, "verbose",             true );
     very_verbose        = get( settings, "very_verbose",        false );

	 verbose = verbose || very_verbose;
     }
	 
std::vector<mign_graph> run()
{
	std::vector<bool> normal_MO;
	
	for ( auto x = 0; x < spec.outputs().size(); x++)
	{
	    const mign_tt_simulator simulator{};
	    const auto r = simulate_mign_function( spec, spec.outputs()[x].first, simulator);
		normal_MO.push_back(!r[0u]); 
	    //return !r[0u];
	}
    
	   
return exact_mig_abc_MO(normal_MO); 
}

std::vector<mign_graph> exact_mig_abc_MO(std::vector<bool> normal_MO)
{
  auto k = start;
  auto depth = 3u; 
  auto fanout = -1; 
  std::vector<mign_graph> mign; 
  std::vector<std::pair<mign_node, std::vector<int>>> node_fo; 
  auto flag = 1; 
  mign_graph mign_best; 
  auto node_local = 0u, node_total = 0u; 
  
  auto total = 0u, total_best = 0u; 
  
  while ( true )
  {
	  
     if ( verbose )
     {
		 std::cout << boost::format( "[i] check for realization with %d gates" ) % k << std::endl;
     }
  
     auto inst = create_inst_MO (normal_MO);
  
     inst->create_var(k, depth, fanout); 
     int start_s=clock();
     inst->create_clauses(node_fo); 
     int stop_s=clock();
	 std::cout << "ALL CLAUSES time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC) << std::endl;
     start_s=clock();
     const auto result = inst->Sat_Solve(); 
	 stop_s=clock();
	 std::cout << "SAT SOLVE time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC) << std::endl;
	 
     if ( result == 1)
       {
	   total = 0; 
	   //inst->print_debug();
	   std::vector<std::pair<mign_node, std::vector<int>>> node_fo_p; 
       mign = inst->extract_mig_MO( model_name, normal_MO, verbose );
	   mign[0] = mign_fo_restricted_opt ( mign[0], 3, 1); 
	   return mign; 
	  
	  /* mign[0].compute_fanout(); 
	   
   	   for ( auto& node : mign[0].topological_nodes())
       {
		   std::vector<int> parents; 
		   if ( mign[0].is_input( node) ) { continue; }
		   if (mign[0].fanout_count(node) <= 3) { continue; }
		   else 
		   {
			   total = total + mign[0].fanout_count(node)%3; 
			   for ( auto& node_two : mign[0].topological_nodes())
			   {
				   if (node_two <= node) { continue; }
				   auto children = mign[0].children(node_two); 
				   for ( auto& c : children )
				   {
					   if ( c == node)
						  parents.push_back(node_two);  
				   }
			   }
			   node_fo_p.push_back(std::make_pair(node, parents)); 
		   }
       }
	   
	   if (flag == 1)
		  {
		  	mign_best = mign[0];
			total_best = total; 
			flag = 0; 
		  } 
		  
	   if (node_fo_p.size() == 0)
		  return mign; 
	   else 
		   node_fo = node_fo_p;  
	   if ((node_local <= 2) && (node_total <= total_best))
	   {
		   node_local++; 
	   }
	   else  if ((node_local > 2) && (node_total <= total_best ))
	   {
		   node_local = 0; 
		   node_total++; 
		   ++k; 
	   }
	   else 
	   {
		   mign[0] = mign_fo_restricted_opt ( mign_best, 3, 1); 
	   	   //mign[0] = rewrite_max_FO (mign_best, 3);  // funziona ancora da scrivere
		   return mign; 
	   }*/
       }
     else if ( result == 2 )
      {
       //last_size = k;
      return std::vector<mign_graph>();
      }
    else
      ++k;
  }
}

inline std::shared_ptr<exact_inst> create_inst_MO(std::vector<bool> normal_MO) const
{
  auto inst = std::make_shared<exact_inst>(spec.inputs().size(),verbose, spec.outputs().size()); 
  inst->tt_from_spec_MO( spec , normal_MO);
  return inst; 
}

private:
  mign_graph spec;
 // std::vector<bool> normal;
  unsigned start;
 // int start_depth; 

  std::string model_name;
  //std::string output_name;
  unsigned objective;
  bool incremental;
  bool all_solutions;
  //std::string breaking;
  //bool enc_with_bitvectors;
  boost::optional<unsigned> timeout;
  bool verbose;
  bool very_verbose;
};


boost::optional<mign_graph> exact_mig_with_sat_abc( const tt& spec,
                                               const properties::ptr& settings,
                                               const properties::ptr& statistics )
{
  // timing 
  properties_timer t( statistics );

  assert( !spec.empty() );

  const auto all_solutions = get( settings, "all_solutions", false );
  exact_mig_abc_manager<mign_graph> mgr( spec_representation_mign( spec ), settings );

  auto start_s=clock();
  const auto migns = mgr.run();
  auto stop_s=clock();
  std::cout << "**********************************************" << std::endl;
  std::cout << "TOTAL SAT SOLVE time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC) << std::endl;
  if ( all_solutions )
  {
    set( statistics, "all_solutions", migns );
  }
 // set( statistics, "last_size", mgr.last_size );

  if ( migns.empty() )
  {
    return boost::none;
  }
  else
  {
    return migns.front();
  }

}


boost::optional<mign_graph> exact_mig_with_sat_abc(const mign_graph& spec,
                                               const properties::ptr& settings,
                                               const properties::ptr& statistics )
{
  // timing 
  properties_timer t( statistics );

  const auto all_solutions = get( settings, "all_solutions", false );

  exact_mig_abc_manager<mign_graph> mgr( spec_representation_mign( spec ), settings );

  auto start_s=clock();
  const auto migns = mgr.run();
  auto stop_s=clock();
  std::cout << "**********************************************" << std::endl;
  std::cout << "TOTAL SAT SOLVE time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC) << std::endl;
  if ( all_solutions )
  {
    set( statistics, "all_solutions", migns );
  }
  //set( statistics, "last_size", mgr.last_size );

  if ( migns.empty() )
  {
    return boost::none;
  }
  else
  {
    return migns.front();
  }

}

boost::optional<mign_graph> exact_mig_with_sat_abc_MO(const mign_graph& spec,
                                               const properties::ptr& settings,
                                               const properties::ptr& statistics)
{
  // timing 

  const auto all_solutions = get( settings, "all_solutions", false );

  exact_mig_abc_manager_MO mgr( spec , settings, statistics );

  auto start_s=clock();
  const auto migns = mgr.run();
  auto stop_s=clock();
  std::cout << "**********************************************" << std::endl;
  std::cout << "TOTAL SAT SOLVE time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC) << std::endl;
  if ( all_solutions )
  {
    set( statistics, "all_solutions", migns );
  }
  //set( statistics, "last_size", mgr.last_size );
  
  if ( migns.empty() )
  {
    return boost::none;
  }
  else
  {
    return migns.front();
  }

}



}

// Local Variables:
// c-basic-offset: 2
// eval: (c-set-offset 'substatement-open 0)
// eval: (c-set-offset 'innamespace 0)
// End:
