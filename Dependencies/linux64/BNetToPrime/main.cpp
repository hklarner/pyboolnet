///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// @brief	The BNetToPrime program that converts a Boolean Network to a list of prime implicants for all the regulatory functions.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#include "source/formulae_resolver.h"
#include "source/implicant_enumerator.h"

bool has_fin;
bool has_fout;

// #define RUN_TESTS


// @brief	The number of the regulators is bounded by the nubmer of bits in the size_t 
size_t maxRegulatorsCount() {
	return sizeof(size_t) * 8;
}

// @brief	from the id obtain the valation of the respective variables (e.g. for id==4 and variables=={A,B,C} we get (A=1,B=0,C=0), for id==1 we get (A=0,B=0,C=1))
Minterm valuationToVals(const size_t valuation_id, map<string, bool> & valuation) {
	Minterm result(valuation.size(), 0);
	int ele = 0;
	for (map<string, bool>::iterator it = valuation.begin(); it != valuation.end(); it++, ele++) {
		bool val = ((valuation_id >> (valuation.size() - 1 - ele)) % 2) == 1;
		result[ele] = val;
		it->second = val;
	}
	return result;
}

// @brief	if # is present, remove everything after it
string removeComment(const string & original) {
	const size_t pos = original.find('#');
	return original.substr(0, pos);
}

//
int main(int argc, char ** argv) {
	try {
#ifdef _MSC_VER //Set the output buffer size for visual studio
		setvbuf(stdout, 0, _IOLBF, 4096);
#endif
#ifdef RUN_TESTS
		FormulaeResolver::test();
#else
		// Parse the input
		if (argc > 1) {
			string arg1 = argv[1];
			if (arg1 == "--help" || arg1 == "-h") {
				IO::printHelp();
				return 0;
			}
			if (arg1 == "--ver" || arg1 == "-v") {
				IO::printVersion();
				return 0;
			}
		}
		has_fin = argc > 1;
		has_fout = argc > 2;

		// Open the input and output files, use standard streams if not specified
		fstream fin;
		if (has_fin) {
			fin.open(argv[1], fstream::in);
			if (!fin) {
				throw invalid_argument(string("Failed to open the input file ") + argv[1]);
			}
		}
		istream & in = has_fin ? fin : cin;

		fstream fout;
		if (has_fout) {
			fout.open(argv[2], fstream::out);
			if (!fout) {
				throw invalid_argument(string("Failed to open the output file ") + argv[2]);
			}
		}
		ostream & out = has_fout ? fout : cout;


		// Holds the input
		map<string, pair<vector<string>, string> > line_data;
		string line;
		// Read computed and write line by line
		while (getline(in, line)) {
            line = FormulaeResolver::removeWhitespaces(line);
			line = removeComment(line);
			// Skip the first line, if it is "targets,factors"
            if (line.empty() || line == "targets,factors" ) {
				continue;
			}
			// Parse the line
			size_t comma_pos = line.find(',');
			string component = line.substr(0, comma_pos);
			if (line_data.count(component)) {
				throw runtime_error(component + " already has a function.");
			}
			string formula = FormulaeResolver::removeWhitespaces(line.substr(comma_pos + 1));
			vector<string> regulators = IO::getAllRegulators(formula);
			line_data.insert(make_pair(component, make_pair(regulators, formula)));
		}

		// Check if all components are present, if not, add self-regulation
		for (map<string, pair<vector<string>, string> >::iterator it = line_data.begin(); it != line_data.end(); it++) {
            for (vector<string>::const_iterator comp_it = it->second.first.begin(); comp_it != it->second.first.end(); comp_it++) {
				if (line_data.count(*comp_it) == 0) {
					vector<string> regulators;
					regulators.push_back(*comp_it);
					line_data.insert(make_pair(*comp_it, make_pair(regulators, *comp_it)));
				}
			}
		}

		// Compute and output data for each line
		out << "{";
        for (map<string, pair<vector<string>, string> >::const_iterator it = line_data.begin(); it != line_data.end(); it++) {
			const string component = it->first;
			const vector<string> regulators = it->second.first;
			const string formula = it->second.second;

			const size_t VALUATIONS_COUNT = static_cast<size_t>(pow(2, regulators.size())); // How many valuations of the variables there are
			if (regulators.size() > maxRegulatorsCount()) {
				throw runtime_error("The component '" + component + "' has too many regulators.");
			}

			// Create the valuation map, also write the current line on the output 
			map<string, bool> valuation;
			IF_HAS_FOUT(cout << "\rTarget: '" << component << "'. Regulators: [";)
            for (vector<string>::const_iterator it = regulators.begin(); it != regulators.end(); it++) {
				IF_HAS_FOUT(cout << *it << ",";)
				valuation.insert(make_pair(*it, false));
			} 
			IF_HAS_FOUT(cout << "]" << endl;)

			//  Resolve the formulas and push the values to the respective vectors
			DNF true_elems;
			DNF false_elems;
			for (size_t valuation_id = 0; valuation_id < VALUATIONS_COUNT; valuation_id++) {
				Minterm new_elem = valuationToVals(valuation_id, valuation);
				if (FormulaeResolver::resolve(valuation, formula)) {
					true_elems.push_back(new_elem);
				}
				else {
					false_elems.push_back(new_elem);
				}
				IF_HAS_FOUT(cout << "\rSolving formula: " << valuation_id + 1 << "/" << VALUATIONS_COUNT;)
			}

			// Compactize and write the output immediatelly
			out << "\"" << component << "\":[";		
			IF_HAS_FOUT(cout << "\r\tComputing implicants for: '!(" << formula << ")'\n";)
			ImplicantEnumerator::compactize(regulators.size(), false_elems);
			IO::printDNF(false_elems, regulators, out);
			false_elems.clear();
			out << ",";
			IF_HAS_FOUT(cout << "\r\tComputing implicants for: '" << formula << "'\n";)
			ImplicantEnumerator::compactize(regulators.size(), true_elems);
			IO::printDNF(true_elems, regulators, out);
			true_elems.clear();
			out << "],";
		}

		// Remove the last comma
        if (!line_data.empty()) {
			REMOVE_LAST
        }
		out << "}" << std::endl << flush;
#endif
	}
	catch (exception & e) {
		cerr << PROGRAM_NAME << " encountered an exception and aborted." << endl;
		cerr << "Exception message: \"" << e.what() << "\"" << endl;
		return 1;
	}

	return 0;
}
