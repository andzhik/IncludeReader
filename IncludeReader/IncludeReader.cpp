// IncludeReader.cpp : Defines the entry point for the console application.
//

#include "stdafx.h"

#include <boost/graph/graphviz.hpp>

using namespace std::tr2::sys;
using namespace std;

typedef std::tuple<string, string, vector<string>> node_tuple;

using namespace boost;

struct VertexProp
{
	string name;
	string root;
	int index;
};

typedef adjacency_list<vecS, vecS, directedS,
	VertexProp> Graph;

typedef graph_traits<Graph>::vertex_descriptor Vertex;

template <class Name>
class VertexWriter {
public:
	VertexWriter(Name _name) : name(_name) {}
	template <class VertexLabel>
	void operator()(std::ostream& out, const VertexLabel& v) const {
		out << "[label=\"" << name[v].name<< "\"]";
	}
private:
	Name name;
};

node_tuple readFile(path currentFile)
{
	regex rx("(^|\\s)#include\\s[\"<](.*?)[\">]");

	string fileName = currentFile.filename();
	transform(fileName.begin(), fileName.end(), fileName.begin(), tolower);
	string fileFolder = currentFile.parent_path();
	transform(fileFolder.begin(), fileFolder.end(), fileFolder.begin(), tolower);

	vector<string> includes;
	ifstream sourceFile(currentFile);
	stringstream buffer;
	buffer << sourceFile.rdbuf();
	sourceFile.close();
	string sourceFileContent(buffer.str());

	sregex_iterator rit(sourceFileContent.begin(), sourceFileContent.end(), rx);
	sregex_iterator riend;

	smatch res;
	string res2;

	while (rit != riend) {
		res = *rit;
		res2 = res[2];
		transform(res2.begin(), res2.end(), res2.begin(), tolower);
		includes.push_back(res2);
		++rit;
	}

	return make_tuple(fileName, fileFolder, includes);
}

Vertex addVertex(Graph &_g, std::string &_file, string &_path);

int _tmain(int argc, _TCHAR* argv[])
{
	namespace po = boost::program_options;

	po::options_description desc("Allowed options");
	desc.add_options()
		("help,h", "Display help")
		("input-path,P", po::value<string>(), "Set the root of source files tree")
		("include,I", po::value<vector<string>>(), "External include paths")
		("output,O", po::value<string>(), "Output dot-file")
		;

	po::variables_map vm;
	po::store(po::parse_command_line(argc, argv, desc), vm);
	po::notify(vm);

	if (vm.count("help") || vm.empty()) 
	{
		cout << desc << "\n";
		return 1;
	}

	path currentPath;
	if (vm.count("input-path") == 1)
	{
		currentPath = path(vm["input-path"].as<string>());
		cout << "Root [input-path] is set to " << currentPath.file_string() << "\n";
	}
	else
	{
		cout << "One [input-path] parameter is required.\n";
		return 1;
	}

	vector<string> includePaths;
	if (vm.count("include"))
		includePaths = vm["include"].as<vector<string>>();

	string outputFile;
	if (vm.count("output") == 1)
	{
		outputFile = vm["output"].as<string>();
		cout << "Output is set to " << outputFile << "\n";
	}
	else
	{
		cout << "One [output] parameter is required.\n";
		return 1;
	}

	int pathLength = currentPath.file_string().size();
	int id = 0;
	set<string> sourceExt = { ".cpp", ".h", ".c" };

	clock_t time1, time2, glob_begin = clock();
	double time_spent;

	vector<future<node_tuple>> results;

	for (recursive_directory_iterator it(currentPath); it != recursive_directory_iterator(); ++it)
	{
		path currentFile = it->path();
		if (is_regular_file(currentFile))
		{
			if (sourceExt.find(currentFile.extension()) == sourceExt.end())
				continue;

			results.push_back(async(launch::async, readFile, currentFile));
		}
	}

	Graph g;

	multimap<string, pair<string, Vertex>> vertices_in_graph;
	map<Vertex, vector<string>> vertex_includes;

	for_each(results.begin(), results.end(),
		[&](decltype(*results.begin()) &_future)
	{
		auto _obj = _future.get();
		Vertex v = addVertex(g, std::get<0>(_obj), std::get<1>(_obj));

		vertex_includes.insert(make_pair(v, std::get<2>(_obj)));

		vertices_in_graph.insert(make_pair(std::get<0>(_obj), make_pair(std::get<1>(_obj), v)));
	});

	time1 = clock();
	time_spent = (double)(time1 - glob_begin) / CLOCKS_PER_SEC;
	std::cout << "Time for file read and regex match: " << time_spent << endl;

	typedef graph_traits<Graph>::edge_descriptor Edge;

	for (auto vertex : vertices_in_graph)
	{
		for (auto include : vertex_includes[vertex.second.second])
		{
			auto node_in_graph = find_if(vertices_in_graph.begin(), vertices_in_graph.end(),
				[&](decltype(*vertices_in_graph.begin()) &_node)
			{
				return include == _node.first;
			});

			if (node_in_graph != vertices_in_graph.end())
			{
				while (node_in_graph != vertices_in_graph.end())
				{
					if (node_in_graph->second.first == vertex.second.first || node_in_graph->second.first == "")
					{
						Edge e;
						e = (add_edge(vertex.second.second, node_in_graph->second.second, g)).first;
						break;
					}

					++node_in_graph;
				}

			}
			if (node_in_graph == vertices_in_graph.end())
			{
				string folder;
				bool added = false;
				Vertex v;
				for (auto includePath : includePaths)
				{
					path external_path = includePath.append(include);
					if (exists(external_path))
					{
						v = addVertex(g, include, includePath);
						vertices_in_graph.insert(make_pair(include, make_pair(includePath, v)));
						added = true;
					}
				}
				if (!added)
				{
					string empty = "";
					v = addVertex(g, include, empty);
					vertices_in_graph.insert(make_pair(include, make_pair(empty, v)));
				}

				Edge e;
				e = (add_edge(vertex.second.second, v, g)).first;
			}
		}
	}
	time2 = clock();
	time_spent = (double)(time2 - time1) / CLOCKS_PER_SEC;
	std::cout << "Building graph: " << time_spent << endl;

	VertexWriter<Graph> writer(g);
	ofstream outf(outputFile);

	clock_t time3 = clock();
	boost::write_graphviz(outf, g, writer);

	time_spent = (double)(time3 - time2) / CLOCKS_PER_SEC;
	std::cout << "Outputting graph: " << time_spent << endl;

	return 0;
}

Vertex addVertex(Graph &_g, std::string &_file, string &_path)
{
	Vertex v = add_vertex(_g);

	VertexProp p;
	p.name = _file;
	p.root = _path;
	p.index = v;
	_g[v] = p;

	return v;
}

