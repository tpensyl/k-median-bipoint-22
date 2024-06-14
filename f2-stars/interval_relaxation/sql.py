import sqlite3, argparse

BASE_PATH = "output/"

def delete_all_entries(n):
	conn = sqlite3.connect(BASE_PATH+f'g{n}/intervals.db', timeout=500)
	cursor = conn.cursor()
	cursor.execute('DELETE FROM Intervals')
	conn.commit()
	conn.close()
	conn = sqlite3.connect(BASE_PATH+f'g{n}/done_intervals.db', timeout=500)
	cursor = conn.cursor()
	cursor.execute('DELETE FROM Intervals')
	conn.commit()
	conn.close()

# Insert multiple entries into the table
def insert_entries(n,entries):
	conn = sqlite3.connect(BASE_PATH+f'g{n}/intervals.db', timeout=500)
	cursor = conn.cursor()
	table_str='''
	INSERT INTO Intervals (obj, b0, b1, {gammaAs})
	VALUES (?, ?, ?, {ques})
	'''.format(gammaAs=get_gamma_str(n,", ",""), ques=", ".join(["?"]*(2*n)))
	cursor.executemany(table_str, entries)
	conn.commit()
	# Close the connection
	conn.close()

def dump_entry(n,interval):
	conn = sqlite3.connect(BASE_PATH+f'g{n}/done_intervals.db', timeout=500)
	cursor = conn.cursor()
	table_str = '''
	INSERT INTO Intervals (obj, b0, b1, {gammaAs}, {vars})
	VALUES (?, ?, ?, {ques})
	'''.format(gammaAs=get_gamma_str(n,", ",""), vars=get_vars_str(n+1,", ",""), ques=", ".join(["?"]*(4*(n+1)*(n+1)+2*n+1)))
	cursor.executemany(table_str, [interval])
	conn.commit()
	# Close the connection
	conn.close()

# Query to return 'limit' entries where obj_val >= 'x'
def query_entries(n,x,limit=1000):
	conn = sqlite3.connect(BASE_PATH+f'g{n}/intervals.db', timeout=500)
	cursor = conn.cursor()
	# Select the entries
	table_str = '''
	SELECT id, obj, b0, b1, {gammaAs}
	FROM Intervals
	WHERE obj >= ?
	ORDER BY obj DESC
	LIMIT ?
	'''.format(gammaAs=get_gamma_str(n,", ",""))
	cursor.execute(table_str, (x,limit,))
	results = cursor.fetchall()

	# Delete the selected entries by their IDs
	if results:
		ids_to_delete = [row[0] for row in results]  # Extract IDs from the results
		cursor.executemany('''
		DELETE FROM Intervals
		WHERE id = ?
		''', [(id,) for id in ids_to_delete])
		conn.commit()
	# Close the connection
	conn.close()
	return results

def get_gamma_str(n,sep=",\n\t\t",pad=" REAL"):
	return sep.join(['gammaA'+str(i)+str(j)+pad for i in range(n) for j in range(2)])

def get_vars_str(n,sep=",\n\t\t",pad=" REAL"):
	vars = ["X"+pad]
	vars += ["d1A"+str(i+1)+"B"+str(j+1)+pad for i in range(n) for j in range(n)]
	vars += ["d1A"+str(i+1)+"C"+str(j+1)+pad for i in range(n) for j in range(n)]
	vars += ["d2A"+str(i+1)+"B"+str(j+1)+pad for i in range(n) for j in range(n)]
	vars += ["d2A"+str(i+1)+"C"+str(j+1)+pad for i in range(n) for j in range(n)]
	return sep.join(vars)

def create_db(n):
	# Database to store Intervals to process
	# Step 1: Connect to the SQLite database (or create it)
	conn = sqlite3.connect(BASE_PATH+f'g{n}/intervals.db',timeout=500)
	cursor = conn.cursor()

	# Step 2: Create a table with 7 floating point columns
	table_str = '''
	CREATE TABLE IF NOT EXISTS Intervals (
		id INTEGER PRIMARY KEY AUTOINCREMENT,
		obj REAL,
		b0 REAL,
		b1 REAL,
		{gammaAs}
	)
	'''.format(gammaAs=get_gamma_str(n))

	cursor.execute(table_str)

	# Step 3: Create an index on the obj_val column
	cursor.execute('CREATE INDEX IF NOT EXISTS idx_obj ON Intervals(obj)')
	conn.commit()
	conn.close()

	# Database for storing processed intervals
	# Step 1: Connect to the SQLite database (or create it)
	conn = sqlite3.connect(BASE_PATH+f'g{n}/done_intervals.db',timeout=500)
	cursor = conn.cursor()

	# Step 2: Create a table with 7 floating point columns
	table2_str = '''
	CREATE TABLE IF NOT EXISTS Intervals (
		id INTEGER PRIMARY KEY AUTOINCREMENT,
		obj REAL,
		b0 REAL,
		b1 REAL,
		{gammaAs},
		{vars}
	)
	'''.format(gammaAs=get_gamma_str(n), vars=get_vars_str(n+1))
	cursor.execute(table2_str)

	# Step 3: Create an index on the obj_val column
	cursor.execute('CREATE INDEX IF NOT EXISTS idx_obj ON Intervals(obj)')
	conn.commit()
	conn.close()