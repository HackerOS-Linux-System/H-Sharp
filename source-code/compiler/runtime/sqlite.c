#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sqlite3.h>

typedef const char* hsh_string;

hsh_string hsh_sqlite_open(hsh_string path) {
    if (!path || !*path) path = "db.sqlite";
    char* h = (char*)malloc(strlen(path) + 1);
    if (h) strcpy(h, path);
    return h ? h : path;
}

hsh_string hsh_sqlite_exec(hsh_string db_path, hsh_string sql) {
    if (!db_path || !sql) return "";
    sqlite3* db;
    if (sqlite3_open(db_path, &db) != SQLITE_OK) {
        const char* err = sqlite3_errmsg(db);
        char* out = (char*)malloc(strlen(err) + 1);
        if (out) strcpy(out, err);
        sqlite3_close(db);
        return out ? out : "";
    }
    char* errmsg = NULL;
    int rc = sqlite3_exec(db, sql, NULL, NULL, &errmsg);
    hsh_string result = "";
    if (rc != SQLITE_OK && errmsg) {
        char* out = (char*)malloc(strlen(errmsg) + 1);
        if (out) strcpy(out, errmsg);
        result = out ? out : "";
        sqlite3_free(errmsg);
    }
    sqlite3_close(db);
    return result;
}

/* Internal: run prepared statement, return CSV rows */
static hsh_string hsh_sqlite_run(hsh_string db_path, hsh_string sql,
                                   hsh_string* binds, int nbinds) {
    if (!db_path || !sql) return "";
    sqlite3* db;
    if (sqlite3_open(db_path, &db) != SQLITE_OK) { sqlite3_close(db); return ""; }
    sqlite3_stmt* stmt;
    if (sqlite3_prepare_v2(db, sql, -1, &stmt, NULL) != SQLITE_OK) {
        const char* err = sqlite3_errmsg(db);
        char* out = (char*)malloc(strlen(err) + 1);
        if (out) strcpy(out, err);
        sqlite3_close(db);
        return out ? out : "";
    }
    for (int i = 0; i < nbinds; i++)
        sqlite3_bind_text(stmt, i + 1, binds[i] ? binds[i] : "", -1, SQLITE_TRANSIENT);

    char* buf = NULL; size_t total = 0, cap = 0;
    int ncols = sqlite3_column_count(stmt);
    while (sqlite3_step(stmt) == SQLITE_ROW) {
        for (int c = 0; c < ncols; c++) {
            const char* cell = (const char*)sqlite3_column_text(stmt, c);
            if (!cell) cell = "";
            size_t clen = strlen(cell);
            size_t needed = clen + 2;
            if (total + needed > cap) {
                cap = (cap + needed) * 2;
                char* nb = (char*)realloc(buf, cap);
                if (!nb) { free(buf); sqlite3_finalize(stmt); sqlite3_close(db); return ""; }
                buf = nb;
            }
            memcpy(buf + total, cell, clen); total += clen;
            buf[total++] = (c == ncols - 1) ? '\n' : ',';
        }
    }
    sqlite3_finalize(stmt);
    sqlite3_close(db);
    if (!buf) return "";
    buf[total] = '\0';
    return buf;
}

hsh_string hsh_sqlite_query(hsh_string db_path, hsh_string sql) {
    return hsh_sqlite_run(db_path, sql, NULL, 0);
}
hsh_string hsh_sqlite_query_bind1(hsh_string db_path, hsh_string sql, hsh_string b1) {
    hsh_string binds[1] = { b1 };
    return hsh_sqlite_run(db_path, sql, binds, 1);
}
hsh_string hsh_sqlite_query_bind2(hsh_string db_path, hsh_string sql, hsh_string b1, hsh_string b2) {
    hsh_string binds[2] = { b1, b2 };
    return hsh_sqlite_run(db_path, sql, binds, 2);
}
hsh_string hsh_sqlite_query_bind3(hsh_string db_path, hsh_string sql,
                                    hsh_string b1, hsh_string b2, hsh_string b3) {
    hsh_string binds[3] = { b1, b2, b3 };
    return hsh_sqlite_run(db_path, sql, binds, 3);
}
void hsh_sqlite_close(hsh_string db_path) { (void)db_path; }
