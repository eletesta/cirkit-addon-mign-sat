/* CirKit: A circuit toolkit
 * Copyright (C) 2009-2015  University of Bremen
 * Copyright (C) 2015-2016  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

#include "exact_mign.hpp"

#include <iostream>

#include <core/utils/program_options.hpp>

#include <classical/cli/stores_experimental.hpp>
#include <classical/mign/mign.hpp>
#include <classical/mig_sat/mig_sat_cegar.hpp>
#include <classical/cli/stores.hpp>

namespace cirkit
{

exact_mign_command::exact_mign_command ( const environment::ptr& env )
	: cirkit_command( env, "Exact MIGn synthesis with constraints" )
{
	opts.add_options()
		( "depth,d",          value_with_default( &depth ),  "maximum depth  (-1 if no constraint on depth)" )
		( "fanout,f",         value_with_default( &fanout ), "maximum fanout (-1 if no constraint on fanout)" )
		( "cegar_option,c",   value_with_default( &option ),  "Option for CEGAR approach: \n 0 : no CEGAR \n 1 : CEGAR on inputs \n 2 : CEGAR on fanout \n 3 : DOUBLE CEGAR \n" )
		;
}

bool exact_mign_command::execute()
{
	   
		auto statistics = std::make_shared<properties>();
		auto settings = std::make_shared<properties>();
		
		auto& migns = env->store<mign_graph>();
		
        if ( migns.current_index() == -1 )
        {
          std::cout << "[w] no migns in store" << std::endl;
          return true;
        }
		
		auto mign = migns.current(); 
	
		if (boost::optional<mign_graph> mign = exact_mig_with_sat_cegar( migns.current(), option, depth, fanout,settings, statistics))
		{
	    	  migns.extend();
	    	  migns.current() = *mign; 
		}
	
	return true;
}

}

// Local Variables:
// c-basic-offset: 2
// eval: (c-set-offset 'substatement-open 0)
// eval: (c-set-offset 'innamespace 0)
// End:
